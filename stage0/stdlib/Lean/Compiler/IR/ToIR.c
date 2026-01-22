// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: public import Lean.Compiler.IR.CompilerM public import Lean.Compiler.IR.ToIRType import Lean.Compiler.IR.UnboxResult import Lean.Compiler.IR.Boxing
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
extern lean_object* l_Lean_IR_instInhabitedArg_default;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__11;
lean_object* l_Lean_IR_hasTrivialStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t l_Lean_IR_IRType_isVoid(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1();
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_findEnvDecl(lean_object*, lean_object*, uint8_t);
uint8_t l_Array_isEmpty___redArg(lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4;
static lean_object* l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__8;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
lean_object* l_Lean_IR_CtorInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__16;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3();
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isErased(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__0;
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1;
static lean_object* l_Lean_IR_ToIR_lowerProj___closed__1;
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__3;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2;
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__15;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__7;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__7;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__13;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0;
static lean_object* l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
lean_object* l_instMonadEST(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__9;
lean_object* l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody_default__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__1;
extern lean_object* l_Lean_IR_declMapExt;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__14;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object*, lean_object*);
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
lean_object* l_Lean_IR_toIRType(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam_default;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6;
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___boxed(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse;
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__6;
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__10;
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__5;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__8;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*);
lean_object* l_Lean_IR_getCtorLayout(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__0;
static lean_object* l_Lean_IR_ToIR_addDecl___redArg___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__2;
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
lean_object* l_instMonadLiftBaseIOEIO___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_IR_nameToIRType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_M_run___redArg___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__4;
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__0;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_instToFormatIRType___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0;
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx(lean_object*);
extern lean_object* l_Lean_IR_instInhabitedExpr_default;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__2;
lean_object* l_instMonadLiftT___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx___boxed(lean_object*);
size_t lean_usize_sub(size_t, size_t);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__5;
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_Lean_Core_liftIOCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__12;
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__4;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5;
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerCode___closed__4;
lean_object* l_Lean_IR_ExplicitBoxing_boxedConstDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_toIR___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__10;
static lean_object* l_Lean_IR_ToIR_lowerDecl___closed__1;
lean_object* l_Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_IR_mkDummyExternDecl(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_lowerLet___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2;
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3;
lean_object* l_instMonadLiftTOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_IR_UnboxResult_hasUnboxAttr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_initFn___lam__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2____boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tagged_return", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mark extern definition to always return tagged values", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ToIR", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("taggedReturnAttr", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_2 = l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_3 = l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_4 = l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_3 = l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_4 = l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_5 = l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_6 = 0;
x_7 = lean_box(2);
x_8 = l_Lean_registerTagAttribute(x_3, x_4, x_2, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Marks an extern definition to be guaranteed to always return tagged values.\nThis information is used to optimize reference counting in the compiler.\n", 149, 149);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_3 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1();
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(24u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(93u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(93u);
x_2 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1;
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(19u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(29u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4;
x_3 = lean_unsigned_to_nat(19u);
x_4 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5;
x_2 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_;
x_3 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_6);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0;
x_2 = l_ReaderT_instMonad___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Core_liftIOCore___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftBaseIOEIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_IO_instMonadLiftSTRealWorldBaseIO___lam__0___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadLiftT___lam__0___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5;
x_2 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10;
x_3 = lean_alloc_closure((void*)(l_instMonadLiftTOfMonadLift___redArg___lam__0), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11;
x_2 = lean_alloc_closure((void*)(l_StateRefT_x27_get), 5, 4);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, lean_box(0));
lean_closure_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_ctor_get(x_3, 3);
x_9 = lean_ctor_get(x_3, 4);
x_10 = lean_ctor_get(x_3, 1);
lean_dec(x_10);
x_11 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_12 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_13 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_6);
x_14 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_14, 0, x_6);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_9);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_8);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_19, 0, x_7);
lean_ctor_set(x_3, 4, x_17);
lean_ctor_set(x_3, 3, x_18);
lean_ctor_set(x_3, 2, x_19);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_16);
lean_ctor_set(x_1, 1, x_13);
x_20 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12;
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_21, 0, lean_box(0));
lean_closure_set(x_21, 1, lean_box(0));
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, lean_box(0));
lean_closure_set(x_21, 4, lean_box(0));
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_11);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 2);
x_24 = lean_ctor_get(x_3, 3);
x_25 = lean_ctor_get(x_3, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_26 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_27 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_28 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_22);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_29, 0, x_22);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_32, 0, x_25);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_24);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_34, 0, x_23);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_1, 0, x_35);
x_36 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12;
x_37 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_37, 0, lean_box(0));
lean_closure_set(x_37, 1, lean_box(0));
lean_closure_set(x_37, 2, x_1);
lean_closure_set(x_37, 3, lean_box(0));
lean_closure_set(x_37, 4, lean_box(0));
lean_closure_set(x_37, 5, x_36);
lean_closure_set(x_37, 6, x_26);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 4);
lean_inc(x_42);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 lean_ctor_release(x_38, 2);
 lean_ctor_release(x_38, 3);
 lean_ctor_release(x_38, 4);
 x_43 = x_38;
} else {
 lean_dec_ref(x_38);
 x_43 = lean_box(0);
}
x_44 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2;
x_45 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_46 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_39);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_47, 0, x_39);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_39);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_50, 0, x_42);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_51, 0, x_41);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_52, 0, x_40);
if (lean_is_scalar(x_43)) {
 x_53 = lean_alloc_ctor(0, 5, 0);
} else {
 x_53 = x_43;
}
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_52);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
x_55 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12;
x_56 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_56, 0, lean_box(0));
lean_closure_set(x_56, 1, lean_box(0));
lean_closure_set(x_56, 2, x_54);
lean_closure_set(x_56, 3, lean_box(0));
lean_closure_set(x_56, 4, lean_box(0));
lean_closure_set(x_56, 5, x_55);
lean_closure_set(x_56, 6, x_44);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_take(x_2);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 3);
x_9 = lean_apply_1(x_1, x_8);
lean_ctor_set(x_6, 3, x_9);
x_10 = lean_st_ref_set(x_2, x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_instMonadFVarSubstStateM___lam__0___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_M_run___redArg___closed__0;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_M_run___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_IR_ToIR_M_run___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_IR_ToIR_M_run___redArg___closed__2;
x_6 = lean_st_mk_ref(x_5);
lean_inc(x_6);
x_7 = lean_apply_4(x_1, x_6, x_2, x_3, lean_box(0));
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_9);
return x_7;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_6);
lean_dec(x_6);
lean_dec(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
}
else
{
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_M_run___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run(x_1, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(163u);
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1;
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3;
x_5 = lean_panic_fn(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_Lean_instBEqFVarId_beq(x_6, x_2);
if (x_9 == 0)
{
x_3 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_7);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_array_get_size(x_4);
x_6 = l_Lean_instHashableFVarId_hash(x_3);
x_7 = 32;
x_8 = lean_uint64_shift_right(x_6, x_7);
x_9 = lean_uint64_xor(x_6, x_8);
x_10 = 16;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = lean_uint64_to_usize(x_12);
x_14 = lean_usize_of_nat(x_5);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
x_17 = lean_usize_land(x_13, x_16);
x_18 = lean_array_uget(x_4, x_17);
x_19 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_1, x_3, x_18);
lean_dec(x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 3);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Lean_Compiler_LCNF_normFVarImp(x_5, x_1, x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_st_ref_get(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = l_Lean_IR_instInhabitedArg_default;
x_13 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_12, x_11, x_9);
lean_dec(x_9);
lean_dec_ref(x_11);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_st_ref_get(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc_ref(x_16);
lean_dec(x_15);
x_17 = l_Lean_IR_instInhabitedArg_default;
x_18 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_17, x_16, x_14);
lean_dec(x_14);
lean_dec_ref(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getFVarValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getFVarValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_panic_fn(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0___redArg(x_6, x_5, x_1);
lean_dec_ref(x_5);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getJoinPointValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_getJoinPointValue(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_instHashableFVarId_hash(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
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
x_26 = l_Lean_instHashableFVarId_hash(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l_Lean_instHashableFVarId_hash(x_2);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 2, x_19);
x_27 = lean_array_uset(x_5, x_18, x_26);
x_28 = lean_unsigned_to_nat(4u);
x_29 = lean_nat_mul(x_25, x_28);
x_30 = lean_unsigned_to_nat(3u);
x_31 = lean_nat_div(x_29, x_30);
lean_dec(x_29);
x_32 = lean_array_get_size(x_27);
x_33 = lean_nat_dec_le(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_27);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_27);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_4, x_35);
lean_dec(x_4);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_19);
x_38 = lean_array_uset(x_5, x_18, x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_mul(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_38);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
}
}
else
{
lean_dec(x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_7, x_10);
lean_ctor_set(x_4, 2, x_11);
lean_ctor_set(x_4, 0, x_9);
x_12 = lean_st_ref_set(x_2, x_4);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
x_17 = lean_ctor_get(x_4, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
lean_inc(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_16, x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_17);
x_23 = lean_st_ref_set(x_2, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_16);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1_spec__2_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_2);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_7, x_1, x_8);
lean_ctor_set(x_5, 0, x_9);
x_10 = lean_st_ref_set(x_3, x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
x_15 = lean_ctor_get(x_5, 2);
x_16 = lean_ctor_get(x_5, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_2);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_13, x_1, x_17);
x_19 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
x_20 = lean_st_ref_set(x_3, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_ctor_set(x_3, 2, x_7);
x_8 = lean_st_ref_set(x_1, x_3);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_13);
x_17 = lean_st_ref_set(x_1, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_newVar___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar___redArg(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
lean_ctor_set(x_4, 2, x_10);
lean_ctor_set(x_4, 1, x_8);
x_11 = lean_st_ref_set(x_2, x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
lean_inc(x_15);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_14, x_1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_15, x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_16);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_15);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_box(1);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_6, x_1, x_7);
lean_ctor_set(x_4, 0, x_8);
x_9 = lean_st_ref_set(x_2, x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_ctor_get(x_4, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_16 = lean_box(1);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0___redArg(x_12, x_1, x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = 0;
x_7 = l_Lean_IR_findEnvDecl(x_5, x_1, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_addDecl___redArg___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_take(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 5);
lean_dec(x_7);
x_8 = l_Lean_IR_declMapExt;
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_box(0);
x_12 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_8, x_6, x_1, x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
lean_ctor_set(x_4, 5, x_13);
lean_ctor_set(x_4, 0, x_12);
x_14 = lean_st_ref_set(x_2, x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get(x_4, 4);
x_22 = lean_ctor_get(x_4, 6);
x_23 = lean_ctor_get(x_4, 7);
x_24 = lean_ctor_get(x_4, 8);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_25 = l_Lean_IR_declMapExt;
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = lean_box(0);
x_29 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_25, x_17, x_1, x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_IR_ToIR_addDecl___redArg___closed__2;
x_31 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_18);
lean_ctor_set(x_31, 2, x_19);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_21);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
x_32 = lean_st_ref_set(x_2, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_3 = x_1;
} else {
 lean_dec_ref(x_1);
 x_3 = lean_box(0);
}
x_8 = lean_cstr_to_nat("4294967296");
x_9 = lean_nat_dec_lt(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_box(8);
x_4 = x_10;
goto block_7;
}
else
{
lean_object* x_11; 
x_11 = lean_box(12);
x_4 = x_11;
goto block_7;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
if (lean_is_scalar(x_3)) {
 x_5 = lean_alloc_ctor(0, 1, 0);
} else {
 x_5 = x_3;
}
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
case 1:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_box(7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
case 2:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get_uint8(x_1, 0);
lean_dec_ref(x_1);
x_20 = lean_uint8_to_nat(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
case 3:
{
uint16_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get_uint16(x_1, 0);
lean_dec_ref(x_1);
x_25 = lean_uint16_to_nat(x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
case 4:
{
uint32_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get_uint32(x_1, 0);
lean_dec_ref(x_1);
x_30 = lean_uint32_to_nat(x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
case 5:
{
uint64_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_35 = lean_uint64_to_nat(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_box(4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
default: 
{
uint64_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get_uint64(x_1, 0);
lean_dec_ref(x_1);
x_40 = lean_uint64_to_nat(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(5);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = l_Lean_IR_ToIR_getFVarValue___redArg(x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg___redArg(x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_TranslatedProj_ctorIdx(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
lean_dec_ref(x_1);
x_4 = lean_apply_1(x_2, x_3);
return x_4;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_TranslatedProj_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_expr_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_TranslatedProj_erased_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_TranslatedProj_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_instInhabitedExpr_default;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_ToIR_instInhabitedTranslatedProj_default;
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
static lean_object* _init_l_Lean_IR_ToIR_lowerProj___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(13);
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
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
case 2:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_3);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_box(5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_alloc_ctor(4, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_box(5);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 2);
lean_inc(x_29);
lean_dec_ref(x_3);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_nat_add(x_31, x_32);
lean_inc(x_30);
x_34 = lean_alloc_ctor(5, 4, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_1);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
default: 
{
lean_object* x_37; 
lean_dec(x_1);
x_37 = l_Lean_IR_ToIR_lowerProj___closed__1;
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerProj(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_instBEqFVarId_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_instBEqFVarId_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_instHashableFVarId_hash(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_instHashableFVarId_hash(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__0___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_IR_ToIR_bindVar_spec__0_spec__1___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec_ref(x_1);
lean_inc(x_6);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_IR_toIRType(x_7, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_18; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_13 = x_11;
} else {
 lean_dec_ref(x_11);
 x_13 = lean_box(0);
}
x_34 = l_Lean_IR_IRType_isVoid(x_12);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_IR_IRType_isErased(x_12);
x_18 = x_35;
goto block_33;
}
else
{
x_18 = x_34;
goto block_33;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_8);
if (lean_is_scalar(x_13)) {
 x_16 = lean_alloc_ctor(0, 1, 0);
} else {
 x_16 = x_13;
}
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
block_33:
{
if (x_18 == 0)
{
lean_dec(x_6);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_st_ref_take(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 3);
x_22 = lean_box(0);
x_23 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_21, x_6, x_22);
lean_ctor_set(x_19, 3, x_23);
x_24 = lean_st_ref_set(x_2, x_19);
x_14 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_ctor_get(x_19, 2);
x_28 = lean_ctor_get(x_19, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_29 = lean_box(0);
x_30 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_28, x_6, x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_st_ref_set(x_2, x_31);
x_14 = lean_box(0);
goto block_17;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_11);
if (x_36 == 0)
{
return x_11;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerParam(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
x_11 = l_Lean_IR_ToIR_lowerParam(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_17 = lean_array_uset(x_14, x_2, x_12);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = l_Lean_IR_ToIR_lowerArg___redArg(x_8, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_12, x_2, x_10);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec_ref(x_3);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_6, x_7, x_3, x_4);
lean_dec(x_4);
return x_8;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3;
x_4 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5;
x_3 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2;
x_9 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6;
lean_inc_ref(x_7);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
lean_ctor_set(x_10, 3, x_7);
x_11 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 5);
x_7 = l_Lean_MessageData_tagWithErrorName(x_2, x_1);
x_8 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16(x_7, x_3, x_4);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16(x_1, x_2, x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_5, x_1);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fget_borrowed(x_2, x_5);
switch (lean_obj_tag(x_16)) {
case 1:
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
x_17 = lean_array_get_borrowed(x_3, x_4, x_5);
lean_inc(x_17);
x_18 = lean_array_push(x_6, x_17);
x_8 = x_18;
x_9 = lean_box(0);
goto block_13;
}
case 2:
{
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
case 3:
{
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
default: 
{
x_8 = x_6;
x_9 = lean_box(0);
goto block_13;
}
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 2);
x_13 = lean_ctor_get(x_8, 3);
x_14 = lean_ctor_get(x_8, 4);
x_15 = lean_ctor_get(x_8, 1);
lean_dec(x_15);
x_16 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_17 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_11);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_18, 0, x_11);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_13);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_23, 0, x_12);
lean_ctor_set(x_8, 4, x_21);
lean_ctor_set(x_8, 3, x_22);
lean_ctor_set(x_8, 2, x_23);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_20);
lean_ctor_set(x_6, 1, x_17);
x_24 = l_ReaderT_instMonad___redArg(x_6);
x_25 = l_Lean_IR_instInhabitedFnBody_default__1;
x_26 = l_instInhabitedOfMonad___redArg(x_24, x_25);
x_27 = lean_panic_fn(x_26, x_1);
x_28 = lean_apply_4(x_27, x_2, x_3, x_4, lean_box(0));
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_29 = lean_ctor_get(x_8, 0);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
x_32 = lean_ctor_get(x_8, 4);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_8);
x_33 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_34 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_29);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_35, 0, x_29);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_29);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_32);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_31);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_40, 0, x_30);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_33);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_39);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_6, 1, x_34);
lean_ctor_set(x_6, 0, x_41);
x_42 = l_ReaderT_instMonad___redArg(x_6);
x_43 = l_Lean_IR_instInhabitedFnBody_default__1;
x_44 = l_instInhabitedOfMonad___redArg(x_42, x_43);
x_45 = lean_panic_fn(x_44, x_1);
x_46 = lean_apply_4(x_45, x_2, x_3, x_4, lean_box(0));
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 4);
lean_inc(x_51);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 x_52 = x_47;
} else {
 lean_dec_ref(x_47);
 x_52 = lean_box(0);
}
x_53 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3;
x_54 = l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4;
lean_inc_ref(x_48);
x_55 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_55, 0, x_48);
x_56 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_56, 0, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_58, 0, x_51);
x_59 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_59, 0, x_50);
x_60 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_60, 0, x_49);
if (lean_is_scalar(x_52)) {
 x_61 = lean_alloc_ctor(0, 5, 0);
} else {
 x_61 = x_52;
}
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
x_63 = l_ReaderT_instMonad___redArg(x_62);
x_64 = l_Lean_IR_instInhabitedFnBody_default__1;
x_65 = l_instInhabitedOfMonad___redArg(x_63, x_64);
x_66 = lean_panic_fn(x_65, x_1);
x_67 = lean_apply_4(x_66, x_2, x_3, x_4, lean_box(0));
return x_67;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_6, x_1);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_Compiler_LCNF_instInhabitedParam_default;
x_19 = lean_array_get_borrowed(x_18, x_2, x_6);
x_20 = lean_nat_dec_eq(x_6, x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = l_Lean_IR_ToIR_bindErased___redArg(x_21, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_dec_ref(x_22);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_take(x_8);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_23, 3);
lean_inc(x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_5);
lean_inc(x_25);
x_28 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_26, x_25, x_27);
lean_ctor_set(x_23, 3, x_28);
x_29 = lean_st_ref_set(x_8, x_23);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
x_33 = lean_ctor_get(x_23, 2);
x_34 = lean_ctor_get(x_23, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
lean_inc(x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_5);
lean_inc(x_30);
x_36 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_34, x_30, x_35);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_32);
lean_ctor_set(x_37, 2, x_33);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_st_ref_set(x_8, x_37);
x_10 = x_4;
x_11 = lean_box(0);
goto block_15;
}
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_6 = x_13;
x_7 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_10;
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
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__1;
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_unsigned_to_nat(188u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_bindErased___redArg(x_7, x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec_ref(x_8);
x_9 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 2);
x_13 = lean_ctor_get(x_1, 3);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_dec(x_14);
x_15 = l_Lean_IR_ToIR_bindVar___redArg(x_11, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
lean_inc(x_8);
lean_inc_ref(x_7);
x_17 = l_Lean_IR_toIRType(x_12, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_IR_ToIR_newVar___redArg(x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_25 = l_Array_extract___redArg(x_5, x_24, x_4);
x_26 = l_Lean_IR_IRType_boxed(x_18);
lean_dec(x_18);
x_27 = lean_array_get_size(x_5);
x_28 = l_Array_extract___redArg(x_5, x_4, x_27);
x_29 = lean_box(7);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_25);
lean_inc(x_20);
x_31 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_31, 0, x_20);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_31);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_16);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_1);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_35 = l_Array_extract___redArg(x_5, x_34, x_4);
x_36 = l_Lean_IR_IRType_boxed(x_18);
lean_dec(x_18);
x_37 = lean_array_get_size(x_5);
x_38 = l_Array_extract___redArg(x_5, x_4, x_37);
x_39 = lean_box(7);
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_35);
lean_inc(x_20);
x_41 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_41, 0, x_20);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_1, 3, x_33);
lean_ctor_set(x_1, 2, x_41);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_16);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_20);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set(x_42, 2, x_40);
lean_ctor_set(x_42, 3, x_1);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_1);
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_1);
x_55 = l_Lean_IR_ToIR_bindVar___redArg(x_53, x_6);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
lean_inc(x_8);
lean_inc_ref(x_7);
x_57 = l_Lean_IR_toIRType(x_54, x_7, x_8);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = l_Lean_IR_ToIR_newVar___redArg(x_6);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_IR_ToIR_lowerCode(x_2, x_6, x_7, x_8);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_65 = l_Array_extract___redArg(x_5, x_64, x_4);
x_66 = l_Lean_IR_IRType_boxed(x_58);
lean_dec(x_58);
x_67 = lean_array_get_size(x_5);
x_68 = l_Array_extract___redArg(x_5, x_4, x_67);
x_69 = lean_box(7);
x_70 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_65);
lean_inc(x_60);
x_71 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_71, 0, x_60);
lean_ctor_set(x_71, 1, x_68);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_56);
lean_ctor_set(x_72, 1, x_66);
lean_ctor_set(x_72, 2, x_71);
lean_ctor_set(x_72, 3, x_62);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_60);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
if (lean_is_scalar(x_63)) {
 x_74 = lean_alloc_ctor(0, 1, 0);
} else {
 x_74 = x_63;
}
lean_ctor_set(x_74, 0, x_73);
return x_74;
}
else
{
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_4);
lean_dec(x_3);
return x_61;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_75 = lean_ctor_get(x_59, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_76 = x_59;
} else {
 lean_dec_ref(x_59);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_57, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_79 = x_57;
} else {
 lean_dec_ref(x_57);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 1, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_54);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_81 = lean_ctor_get(x_55, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_82 = x_55;
} else {
 lean_dec_ref(x_55);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_16 = l_Lean_IR_toIRType(x_11, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set(x_1, 2, x_21);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_1, 3, x_22);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_free_object(x_1);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_14, 0);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_33 = l_Lean_IR_ToIR_bindVar___redArg(x_31, x_5);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_7);
lean_inc_ref(x_6);
x_35 = l_Lean_IR_toIRType(x_32, x_6, x_7);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
x_37 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_40, 0, x_3);
lean_ctor_set(x_40, 1, x_4);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_38);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 1, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
lean_dec(x_36);
lean_dec(x_34);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_37;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_32);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_47 = x_33;
} else {
 lean_dec_ref(x_33);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 3);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_box(7);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_1, 2, x_20);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_box(7);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_1, 3, x_21);
lean_ctor_set(x_1, 2, x_23);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
}
else
{
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_16;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_IR_ToIR_bindVar___redArg(x_28, x_5);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(7);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_32);
if (lean_is_scalar(x_33)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_33;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_dec(x_30);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_31;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 x_39 = x_29;
} else {
 lean_dec_ref(x_29);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_10, x_4);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_10, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_4);
x_14 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_5, x_6, x_7, x_8);
return x_15;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__3;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(263u);
x_4 = l_Lean_IR_ToIR_lowerLet___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dependsOnNoncomputable", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__6;
x_2 = l_Lean_IR_ToIR_lowerLet___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` not supported by code generator; consider marking definition as `noncomputable`", 81, 81);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerLet___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerLet___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code generator does not support recursor `", 42, 42);
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
x_1 = lean_mk_string_unchecked("` yet, consider using 'match ... with' and/or structural recursion", 66, 66);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = l_Lean_IR_ToIR_bindVar___redArg(x_10, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_7);
lean_inc_ref(x_6);
x_16 = l_Lean_IR_toIRType(x_11, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = l_Lean_IR_IRType_boxed(x_17);
lean_dec(x_17);
x_22 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set(x_1, 2, x_22);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_IR_IRType_boxed(x_17);
lean_dec(x_17);
x_25 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_1, 3, x_23);
lean_ctor_set(x_1, 2, x_25);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_15);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_1);
return x_26;
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_free_object(x_1);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_18;
}
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_free_object(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_1);
lean_dec_ref(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
return x_14;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_1);
x_35 = l_Lean_IR_ToIR_bindVar___redArg(x_33, x_5);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = l_Lean_IR_toIRType(x_34, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_IR_ToIR_lowerCode(x_2, x_5, x_6, x_7);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = l_Lean_IR_IRType_boxed(x_38);
lean_dec(x_38);
x_43 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_4);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_40);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(0, 1, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_39;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_36);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_47 = x_37;
} else {
 lean_dec_ref(x_37);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_34);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_50 = x_35;
} else {
 lean_dec_ref(x_35);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_st_ref_get(x_3);
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get(x_1, 3);
x_18 = lean_ctor_get(x_14, 3);
lean_inc_ref(x_18);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 lean_ctor_release(x_14, 2);
 lean_ctor_release(x_14, 3);
 x_19 = x_14;
} else {
 lean_dec_ref(x_14);
 x_19 = lean_box(0);
}
x_20 = 0;
lean_inc(x_17);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_18, x_17, x_20);
lean_dec_ref(x_18);
switch (lean_obj_tag(x_21)) {
case 0:
{
uint8_t x_22; 
lean_inc(x_15);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_IR_ToIR_lowerLitValue(x_23);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_ctor_set_tag(x_21, 11);
lean_ctor_set(x_21, 0, x_27);
if (lean_is_scalar(x_19)) {
 x_32 = lean_alloc_ctor(0, 4, 0);
} else {
 x_32 = x_19;
}
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_ctor_set_tag(x_21, 11);
lean_ctor_set(x_21, 0, x_27);
if (lean_is_scalar(x_19)) {
 x_34 = lean_alloc_ctor(0, 4, 0);
} else {
 x_34 = x_19;
}
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_free_object(x_21);
lean_dec(x_19);
return x_29;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_21);
lean_dec_ref(x_23);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
return x_24;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_24, 0);
lean_inc(x_37);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_IR_ToIR_lowerLitValue(x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec_ref(x_42);
x_45 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_48, 0, x_43);
if (lean_is_scalar(x_19)) {
 x_49 = lean_alloc_ctor(0, 4, 0);
} else {
 x_49 = x_19;
}
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_46);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_19);
return x_45;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_39);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_52 = x_40;
} else {
 lean_dec_ref(x_40);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
return x_53;
}
}
}
case 1:
{
lean_object* x_54; 
lean_dec(x_19);
x_54 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_54;
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_inc(x_15);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_21, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_21, 2);
lean_inc(x_57);
lean_dec_ref(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_55);
x_58 = l_Lean_IR_hasTrivialStructure_x3f(x_55, x_4, x_5);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
if (lean_obj_tag(x_59) == 1)
{
uint8_t x_60; 
lean_dec(x_55);
lean_dec(x_19);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_61, 2);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_nat_dec_eq(x_62, x_56);
lean_dec(x_56);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_free_object(x_59);
lean_dec(x_57);
x_64 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
lean_dec_ref(x_64);
x_65 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
return x_64;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_inc(x_67);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_st_ref_take(x_3);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_69, 3);
lean_ctor_set(x_59, 0, x_57);
x_72 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_71, x_15, x_59);
lean_ctor_set(x_69, 3, x_72);
x_73 = lean_st_ref_set(x_3, x_69);
x_74 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_69, 0);
x_76 = lean_ctor_get(x_69, 1);
x_77 = lean_ctor_get(x_69, 2);
x_78 = lean_ctor_get(x_69, 3);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_69);
lean_ctor_set(x_59, 0, x_57);
x_79 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_78, x_15, x_59);
x_80 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_80, 0, x_75);
lean_ctor_set(x_80, 1, x_76);
lean_ctor_set(x_80, 2, x_77);
lean_ctor_set(x_80, 3, x_79);
x_81 = lean_st_ref_set(x_3, x_80);
x_82 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_59, 0);
lean_inc(x_83);
lean_dec(x_59);
x_84 = lean_ctor_get(x_83, 2);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_nat_dec_eq(x_84, x_56);
lean_dec(x_56);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_57);
x_86 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
lean_dec_ref(x_86);
x_87 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_91 = lean_st_ref_take(x_3);
x_92 = lean_ctor_get(x_91, 0);
lean_inc_ref(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_91, 2);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 3);
lean_inc_ref(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 lean_ctor_release(x_91, 2);
 lean_ctor_release(x_91, 3);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_57);
x_98 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_95, x_15, x_97);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(0, 4, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_93);
lean_ctor_set(x_99, 2, x_94);
lean_ctor_set(x_99, 3, x_98);
x_100 = lean_st_ref_set(x_3, x_99);
x_101 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_101;
}
}
}
else
{
lean_object* x_102; 
lean_dec(x_59);
x_102 = l_Lean_IR_ToIR_getFVarValue___redArg(x_57, x_3);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_st_ref_get(x_5);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
lean_dec(x_105);
x_107 = l_Lean_Environment_find_x3f(x_106, x_55, x_20);
if (lean_obj_tag(x_107) == 1)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
if (lean_obj_tag(x_108) == 5)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc_ref(x_109);
lean_dec_ref(x_108);
x_110 = lean_ctor_get(x_109, 4);
lean_inc(x_110);
lean_dec_ref(x_109);
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 1);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec_ref(x_110);
lean_inc(x_5);
lean_inc_ref(x_4);
x_113 = l_Lean_IR_getCtorLayout(x_112, x_4, x_5);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_116);
lean_dec(x_114);
x_117 = lean_box(0);
x_118 = lean_array_get(x_117, x_116, x_56);
lean_dec(x_56);
lean_dec_ref(x_116);
x_119 = l_Lean_IR_ToIR_lowerProj(x_104, x_115, x_118);
lean_dec_ref(x_115);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc_ref(x_122);
lean_dec_ref(x_120);
x_123 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
if (lean_is_scalar(x_19)) {
 x_128 = lean_alloc_ctor(0, 4, 0);
} else {
 x_128 = x_19;
}
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_121);
lean_ctor_set(x_128, 2, x_122);
lean_ctor_set(x_128, 3, x_127);
lean_ctor_set(x_125, 0, x_128);
return x_125;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_dec(x_125);
if (lean_is_scalar(x_19)) {
 x_130 = lean_alloc_ctor(0, 4, 0);
} else {
 x_130 = x_19;
}
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_dec(x_124);
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_19);
return x_125;
}
}
else
{
uint8_t x_132; 
lean_dec_ref(x_122);
lean_dec(x_121);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_132 = !lean_is_exclusive(x_123);
if (x_132 == 0)
{
return x_123;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_123, 0);
lean_inc(x_133);
lean_dec(x_123);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; 
lean_dec_ref(x_119);
lean_dec(x_19);
x_135 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
lean_dec_ref(x_135);
x_136 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_136;
}
else
{
uint8_t x_137; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_137 = !lean_is_exclusive(x_135);
if (x_137 == 0)
{
return x_135;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
lean_dec(x_135);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_104);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_140 = !lean_is_exclusive(x_113);
if (x_140 == 0)
{
return x_113;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_113, 0);
lean_inc(x_141);
lean_dec(x_113);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
return x_142;
}
}
}
else
{
lean_dec_ref(x_110);
lean_dec(x_104);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_56);
lean_dec(x_19);
lean_dec(x_15);
lean_dec_ref(x_2);
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
x_10 = lean_box(0);
goto block_13;
}
}
else
{
lean_object* x_143; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_19);
x_143 = l_Lean_IR_ToIR_bindErased___redArg(x_15, x_3);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec_ref(x_143);
x_144 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_144;
}
else
{
uint8_t x_145; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
return x_143;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_148 = !lean_is_exclusive(x_102);
if (x_148 == 0)
{
return x_102;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_102, 0);
lean_inc(x_149);
lean_dec(x_102);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_151 = !lean_is_exclusive(x_58);
if (x_151 == 0)
{
return x_58;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_58, 0);
lean_inc(x_152);
lean_dec(x_58);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
case 3:
{
lean_object* x_154; lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_21, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_21, 2);
lean_inc_ref(x_155);
lean_dec_ref(x_21);
x_156 = lean_array_size(x_155);
x_157 = 0;
lean_inc_ref(x_155);
x_158 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_156, x_157, x_155, x_3);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
lean_inc(x_154);
x_160 = l_Lean_IR_ToIR_findDecl___redArg(x_154, x_5);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
if (lean_obj_tag(x_161) == 1)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_155);
lean_dec(x_19);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_Lean_IR_Decl_params(x_162);
lean_dec(x_162);
x_164 = lean_array_get_size(x_163);
lean_dec_ref(x_163);
x_165 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_154, x_164, x_159, x_3, x_4, x_5);
return x_165;
}
else
{
lean_object* x_166; 
lean_dec(x_161);
lean_inc(x_154);
x_166 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_154, x_5);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
if (lean_obj_tag(x_167) == 1)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_155);
lean_dec(x_19);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_ctor_get(x_168, 3);
lean_inc_ref(x_169);
lean_dec(x_168);
x_170 = lean_array_get_size(x_169);
lean_dec_ref(x_169);
x_171 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_154, x_170, x_159, x_3, x_4, x_5);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
x_172 = lean_st_ref_get(x_5);
x_173 = lean_ctor_get(x_172, 0);
lean_inc_ref(x_173);
lean_dec(x_172);
lean_inc(x_154);
x_174 = l_Lean_Environment_find_x3f(x_173, x_154, x_20);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_175 = l_Lean_IR_ToIR_lowerLet___closed__4;
x_176 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_175, x_3, x_4, x_5);
return x_176;
}
else
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_174);
if (x_177 == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_174, 0);
switch (lean_obj_tag(x_178)) {
case 0:
{
uint8_t x_179; 
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_180 = lean_ctor_get(x_178, 0);
lean_dec(x_180);
x_181 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_182 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_183 = 1;
x_184 = l_Lean_Name_toString(x_154, x_183);
lean_ctor_set_tag(x_178, 3);
lean_ctor_set(x_178, 0, x_184);
x_185 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_178);
x_186 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_MessageData_ofFormat(x_187);
x_189 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_181, x_188, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_178);
x_190 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_191 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_192 = 1;
x_193 = l_Lean_Name_toString(x_154, x_192);
x_194 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_197 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_MessageData_ofFormat(x_197);
x_199 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_190, x_198, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_199;
}
}
case 2:
{
uint8_t x_200; 
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_178);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_201 = lean_ctor_get(x_178, 0);
lean_dec(x_201);
x_202 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_203 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_204 = 1;
x_205 = l_Lean_Name_toString(x_154, x_204);
lean_ctor_set_tag(x_178, 3);
lean_ctor_set(x_178, 0, x_205);
x_206 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_178);
x_207 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_208 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_MessageData_ofFormat(x_208);
x_210 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_202, x_209, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_178);
x_211 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_212 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_213 = 1;
x_214 = l_Lean_Name_toString(x_154, x_213);
x_215 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_216 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_216, 0, x_212);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_218 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_MessageData_ofFormat(x_218);
x_220 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_211, x_219, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_220;
}
}
case 4:
{
uint8_t x_221; 
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_221 = !lean_is_exclusive(x_178);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_222 = lean_ctor_get(x_178, 0);
lean_dec(x_222);
x_223 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_224 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_225 = 1;
x_226 = l_Lean_Name_toString(x_154, x_225);
lean_ctor_set_tag(x_178, 3);
lean_ctor_set(x_178, 0, x_226);
x_227 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_178);
x_228 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_229 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_MessageData_ofFormat(x_229);
x_231 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_223, x_230, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_178);
x_232 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_233 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_234 = 1;
x_235 = l_Lean_Name_toString(x_154, x_234);
x_236 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_237, 0, x_233);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_239 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = l_Lean_MessageData_ofFormat(x_239);
x_241 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_232, x_240, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_241;
}
}
case 5:
{
uint8_t x_242; 
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_242 = !lean_is_exclusive(x_178);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_243 = lean_ctor_get(x_178, 0);
lean_dec(x_243);
x_244 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_245 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_246 = 1;
x_247 = l_Lean_Name_toString(x_154, x_246);
lean_ctor_set_tag(x_178, 3);
lean_ctor_set(x_178, 0, x_247);
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_178);
x_249 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_250 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = l_Lean_MessageData_ofFormat(x_250);
x_252 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_244, x_251, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_178);
x_253 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_254 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_255 = 1;
x_256 = l_Lean_Name_toString(x_154, x_255);
x_257 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_260 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_MessageData_ofFormat(x_260);
x_262 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_253, x_261, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_262;
}
}
case 6:
{
uint8_t x_263; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_dec_ref(x_1);
x_263 = !lean_is_exclusive(x_178);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_178, 0);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 2);
lean_inc(x_266);
x_267 = lean_ctor_get(x_264, 3);
lean_inc(x_267);
lean_dec_ref(x_264);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_265);
x_268 = l_Lean_IR_hasTrivialStructure_x3f(x_265, x_4, x_5);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
lean_dec_ref(x_268);
if (lean_obj_tag(x_269) == 1)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_free_object(x_178);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
lean_dec_ref(x_269);
x_271 = lean_st_ref_take(x_3);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 2);
lean_inc(x_273);
lean_dec(x_270);
x_274 = !lean_is_exclusive(x_271);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_275 = lean_ctor_get(x_271, 3);
x_276 = lean_box(0);
x_277 = lean_nat_add(x_272, x_273);
lean_dec(x_273);
lean_dec(x_272);
x_278 = lean_array_get(x_276, x_155, x_277);
lean_dec(x_277);
lean_dec_ref(x_155);
x_279 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_275, x_15, x_278);
lean_ctor_set(x_271, 3, x_279);
x_280 = lean_st_ref_set(x_3, x_271);
x_281 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_282 = lean_ctor_get(x_271, 0);
x_283 = lean_ctor_get(x_271, 1);
x_284 = lean_ctor_get(x_271, 2);
x_285 = lean_ctor_get(x_271, 3);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_271);
x_286 = lean_box(0);
x_287 = lean_nat_add(x_272, x_273);
lean_dec(x_273);
lean_dec(x_272);
x_288 = lean_array_get(x_286, x_155, x_287);
lean_dec(x_287);
lean_dec_ref(x_155);
x_289 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_285, x_15, x_288);
x_290 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_290, 0, x_282);
lean_ctor_set(x_290, 1, x_283);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_289);
x_291 = lean_st_ref_set(x_3, x_290);
x_292 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_292;
}
}
else
{
lean_object* x_293; 
lean_dec(x_269);
lean_dec_ref(x_155);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_265);
x_293 = l_Lean_IR_nameToIRType(x_265, x_4, x_5);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; uint8_t x_295; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
lean_dec_ref(x_293);
x_295 = l_Lean_IR_IRType_isScalar(x_294);
if (x_295 == 0)
{
lean_object* x_296; 
lean_dec(x_294);
lean_dec(x_266);
lean_free_object(x_178);
lean_free_object(x_174);
lean_inc(x_5);
lean_inc_ref(x_4);
x_296 = l_Lean_IR_getCtorLayout(x_154, x_4, x_5);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
x_302 = lean_ctor_get(x_297, 0);
lean_inc_ref(x_302);
x_303 = lean_ctor_get(x_297, 1);
lean_inc_ref(x_303);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_304 = x_297;
} else {
 lean_dec_ref(x_297);
 x_304 = lean_box(0);
}
x_305 = lean_array_get_size(x_159);
x_306 = l_Array_extract___redArg(x_159, x_267, x_305);
lean_dec(x_159);
x_307 = lean_array_get_size(x_306);
x_308 = lean_array_get_size(x_303);
x_309 = lean_nat_dec_eq(x_307, x_308);
if (x_309 == 0)
{
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_265);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_301;
}
else
{
if (x_295 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_298);
x_310 = l_Lean_IR_instInhabitedArg_default;
x_311 = lean_unsigned_to_nat(0u);
x_312 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_313 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(x_308, x_303, x_310, x_306, x_311, x_312);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
lean_dec_ref(x_315);
x_332 = lean_st_ref_get(x_5);
x_333 = lean_ctor_get(x_332, 0);
lean_inc_ref(x_333);
lean_dec(x_332);
x_334 = l_Lean_IR_UnboxResult_hasUnboxAttr(x_333, x_265);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec_ref(x_16);
x_335 = l_Lean_IR_CtorInfo_type(x_302);
x_317 = x_335;
x_318 = x_3;
x_319 = x_4;
x_320 = x_5;
x_321 = lean_box(0);
goto block_331;
}
else
{
lean_object* x_336; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_336 = l_Lean_IR_toIRType(x_16, x_4, x_5);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
lean_dec_ref(x_336);
x_317 = x_337;
x_318 = x_3;
x_319 = x_4;
x_320 = x_5;
x_321 = lean_box(0);
goto block_331;
}
else
{
uint8_t x_338; 
lean_dec(x_316);
lean_dec(x_314);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_338 = !lean_is_exclusive(x_336);
if (x_338 == 0)
{
return x_336;
}
else
{
lean_object* x_339; lean_object* x_340; 
x_339 = lean_ctor_get(x_336, 0);
lean_inc(x_339);
lean_dec(x_336);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
return x_340;
}
}
}
block_331:
{
lean_object* x_322; 
lean_inc(x_316);
lean_inc_ref(x_302);
x_322 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_302, x_303, x_306, x_316, x_318, x_319, x_320);
lean_dec_ref(x_306);
lean_dec_ref(x_303);
if (lean_obj_tag(x_322) == 0)
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_322, 0);
if (lean_is_scalar(x_304)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_304;
}
lean_ctor_set(x_325, 0, x_302);
lean_ctor_set(x_325, 1, x_314);
if (lean_is_scalar(x_19)) {
 x_326 = lean_alloc_ctor(0, 4, 0);
} else {
 x_326 = x_19;
}
lean_ctor_set(x_326, 0, x_316);
lean_ctor_set(x_326, 1, x_317);
lean_ctor_set(x_326, 2, x_325);
lean_ctor_set(x_326, 3, x_324);
lean_ctor_set(x_322, 0, x_326);
return x_322;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_327 = lean_ctor_get(x_322, 0);
lean_inc(x_327);
lean_dec(x_322);
if (lean_is_scalar(x_304)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_304;
}
lean_ctor_set(x_328, 0, x_302);
lean_ctor_set(x_328, 1, x_314);
if (lean_is_scalar(x_19)) {
 x_329 = lean_alloc_ctor(0, 4, 0);
} else {
 x_329 = x_19;
}
lean_ctor_set(x_329, 0, x_316);
lean_ctor_set(x_329, 1, x_317);
lean_ctor_set(x_329, 2, x_328);
lean_ctor_set(x_329, 3, x_327);
x_330 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
else
{
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_314);
lean_dec(x_304);
lean_dec_ref(x_302);
lean_dec(x_19);
return x_322;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_314);
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_265);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_341 = !lean_is_exclusive(x_315);
if (x_341 == 0)
{
return x_315;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_315, 0);
lean_inc(x_342);
lean_dec(x_315);
x_343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_343, 0, x_342);
return x_343;
}
}
}
else
{
uint8_t x_344; 
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_265);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_344 = !lean_is_exclusive(x_313);
if (x_344 == 0)
{
return x_313;
}
else
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_313, 0);
lean_inc(x_345);
lean_dec(x_313);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_345);
return x_346;
}
}
}
else
{
lean_dec_ref(x_306);
lean_dec(x_304);
lean_dec_ref(x_303);
lean_dec_ref(x_302);
lean_dec(x_265);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_301;
}
}
block_301:
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_box(12);
if (lean_is_scalar(x_298)) {
 x_300 = lean_alloc_ctor(0, 1, 0);
} else {
 x_300 = x_298;
}
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
else
{
uint8_t x_347; 
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_159);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_347 = !lean_is_exclusive(x_296);
if (x_347 == 0)
{
return x_296;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_296, 0);
lean_inc(x_348);
lean_dec(x_296);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
}
}
else
{
lean_object* x_350; 
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_159);
lean_dec(x_154);
lean_dec_ref(x_16);
x_350 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec_ref(x_350);
x_352 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_352) == 0)
{
uint8_t x_353; 
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_352, 0);
lean_ctor_set_tag(x_178, 0);
lean_ctor_set(x_178, 0, x_266);
lean_ctor_set_tag(x_174, 11);
if (lean_is_scalar(x_19)) {
 x_355 = lean_alloc_ctor(0, 4, 0);
} else {
 x_355 = x_19;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_294);
lean_ctor_set(x_355, 2, x_174);
lean_ctor_set(x_355, 3, x_354);
lean_ctor_set(x_352, 0, x_355);
return x_352;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_352, 0);
lean_inc(x_356);
lean_dec(x_352);
lean_ctor_set_tag(x_178, 0);
lean_ctor_set(x_178, 0, x_266);
lean_ctor_set_tag(x_174, 11);
if (lean_is_scalar(x_19)) {
 x_357 = lean_alloc_ctor(0, 4, 0);
} else {
 x_357 = x_19;
}
lean_ctor_set(x_357, 0, x_351);
lean_ctor_set(x_357, 1, x_294);
lean_ctor_set(x_357, 2, x_174);
lean_ctor_set(x_357, 3, x_356);
x_358 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_358, 0, x_357);
return x_358;
}
}
else
{
lean_dec(x_351);
lean_dec(x_294);
lean_dec(x_266);
lean_free_object(x_178);
lean_free_object(x_174);
lean_dec(x_19);
return x_352;
}
}
else
{
uint8_t x_359; 
lean_dec(x_294);
lean_dec(x_266);
lean_free_object(x_178);
lean_free_object(x_174);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_359 = !lean_is_exclusive(x_350);
if (x_359 == 0)
{
return x_350;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_350, 0);
lean_inc(x_360);
lean_dec(x_350);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
return x_361;
}
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_free_object(x_178);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_362 = !lean_is_exclusive(x_293);
if (x_362 == 0)
{
return x_293;
}
else
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_293, 0);
lean_inc(x_363);
lean_dec(x_293);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
return x_364;
}
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
lean_free_object(x_178);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_365 = !lean_is_exclusive(x_268);
if (x_365 == 0)
{
return x_268;
}
else
{
lean_object* x_366; lean_object* x_367; 
x_366 = lean_ctor_get(x_268, 0);
lean_inc(x_366);
lean_dec(x_268);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
}
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_368 = lean_ctor_get(x_178, 0);
lean_inc(x_368);
lean_dec(x_178);
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_368, 3);
lean_inc(x_371);
lean_dec_ref(x_368);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_369);
x_372 = l_Lean_IR_hasTrivialStructure_x3f(x_369, x_4, x_5);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec_ref(x_372);
if (lean_obj_tag(x_373) == 1)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec_ref(x_373);
x_375 = lean_st_ref_take(x_3);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_374, 2);
lean_inc(x_377);
lean_dec(x_374);
x_378 = lean_ctor_get(x_375, 0);
lean_inc_ref(x_378);
x_379 = lean_ctor_get(x_375, 1);
lean_inc_ref(x_379);
x_380 = lean_ctor_get(x_375, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_375, 3);
lean_inc_ref(x_381);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_382 = x_375;
} else {
 lean_dec_ref(x_375);
 x_382 = lean_box(0);
}
x_383 = lean_box(0);
x_384 = lean_nat_add(x_376, x_377);
lean_dec(x_377);
lean_dec(x_376);
x_385 = lean_array_get(x_383, x_155, x_384);
lean_dec(x_384);
lean_dec_ref(x_155);
x_386 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_381, x_15, x_385);
if (lean_is_scalar(x_382)) {
 x_387 = lean_alloc_ctor(0, 4, 0);
} else {
 x_387 = x_382;
}
lean_ctor_set(x_387, 0, x_378);
lean_ctor_set(x_387, 1, x_379);
lean_ctor_set(x_387, 2, x_380);
lean_ctor_set(x_387, 3, x_386);
x_388 = lean_st_ref_set(x_3, x_387);
x_389 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_389;
}
else
{
lean_object* x_390; 
lean_dec(x_373);
lean_dec_ref(x_155);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_369);
x_390 = l_Lean_IR_nameToIRType(x_369, x_4, x_5);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
lean_dec_ref(x_390);
x_392 = l_Lean_IR_IRType_isScalar(x_391);
if (x_392 == 0)
{
lean_object* x_393; 
lean_dec(x_391);
lean_dec(x_370);
lean_free_object(x_174);
lean_inc(x_5);
lean_inc_ref(x_4);
x_393 = l_Lean_IR_getCtorLayout(x_154, x_4, x_5);
if (lean_obj_tag(x_393) == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_395 = x_393;
} else {
 lean_dec_ref(x_393);
 x_395 = lean_box(0);
}
x_399 = lean_ctor_get(x_394, 0);
lean_inc_ref(x_399);
x_400 = lean_ctor_get(x_394, 1);
lean_inc_ref(x_400);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_401 = x_394;
} else {
 lean_dec_ref(x_394);
 x_401 = lean_box(0);
}
x_402 = lean_array_get_size(x_159);
x_403 = l_Array_extract___redArg(x_159, x_371, x_402);
lean_dec(x_159);
x_404 = lean_array_get_size(x_403);
x_405 = lean_array_get_size(x_400);
x_406 = lean_nat_dec_eq(x_404, x_405);
if (x_406 == 0)
{
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec_ref(x_399);
lean_dec(x_369);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_398;
}
else
{
if (x_392 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_395);
x_407 = l_Lean_IR_instInhabitedArg_default;
x_408 = lean_unsigned_to_nat(0u);
x_409 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_410 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(x_405, x_400, x_407, x_403, x_408, x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
lean_dec_ref(x_410);
x_412 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_426; lean_object* x_427; uint8_t x_428; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec_ref(x_412);
x_426 = lean_st_ref_get(x_5);
x_427 = lean_ctor_get(x_426, 0);
lean_inc_ref(x_427);
lean_dec(x_426);
x_428 = l_Lean_IR_UnboxResult_hasUnboxAttr(x_427, x_369);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec_ref(x_16);
x_429 = l_Lean_IR_CtorInfo_type(x_399);
x_414 = x_429;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_430; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_430 = l_Lean_IR_toIRType(x_16, x_4, x_5);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
x_414 = x_431;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_413);
lean_dec(x_411);
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec_ref(x_399);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_432 = lean_ctor_get(x_430, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_433 = x_430;
} else {
 lean_dec_ref(x_430);
 x_433 = lean_box(0);
}
if (lean_is_scalar(x_433)) {
 x_434 = lean_alloc_ctor(1, 1, 0);
} else {
 x_434 = x_433;
}
lean_ctor_set(x_434, 0, x_432);
return x_434;
}
}
block_425:
{
lean_object* x_419; 
lean_inc(x_413);
lean_inc_ref(x_399);
x_419 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_399, x_400, x_403, x_413, x_415, x_416, x_417);
lean_dec_ref(x_403);
lean_dec_ref(x_400);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_421 = x_419;
} else {
 lean_dec_ref(x_419);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_401;
}
lean_ctor_set(x_422, 0, x_399);
lean_ctor_set(x_422, 1, x_411);
if (lean_is_scalar(x_19)) {
 x_423 = lean_alloc_ctor(0, 4, 0);
} else {
 x_423 = x_19;
}
lean_ctor_set(x_423, 0, x_413);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_422);
lean_ctor_set(x_423, 3, x_420);
if (lean_is_scalar(x_421)) {
 x_424 = lean_alloc_ctor(0, 1, 0);
} else {
 x_424 = x_421;
}
lean_ctor_set(x_424, 0, x_423);
return x_424;
}
else
{
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_411);
lean_dec(x_401);
lean_dec_ref(x_399);
lean_dec(x_19);
return x_419;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_411);
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec_ref(x_399);
lean_dec(x_369);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_435 = lean_ctor_get(x_412, 0);
lean_inc(x_435);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_436 = x_412;
} else {
 lean_dec_ref(x_412);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 1, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec_ref(x_399);
lean_dec(x_369);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_438 = lean_ctor_get(x_410, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 x_439 = x_410;
} else {
 lean_dec_ref(x_410);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 1, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_438);
return x_440;
}
}
else
{
lean_dec_ref(x_403);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec_ref(x_399);
lean_dec(x_369);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_398;
}
}
block_398:
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_box(12);
if (lean_is_scalar(x_395)) {
 x_397 = lean_alloc_ctor(0, 1, 0);
} else {
 x_397 = x_395;
}
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_159);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_441 = lean_ctor_get(x_393, 0);
lean_inc(x_441);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 x_442 = x_393;
} else {
 lean_dec_ref(x_393);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 1, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_441);
return x_443;
}
}
else
{
lean_object* x_444; 
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_159);
lean_dec(x_154);
lean_dec_ref(x_16);
x_444 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
lean_dec_ref(x_444);
x_446 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_448 = x_446;
} else {
 lean_dec_ref(x_446);
 x_448 = lean_box(0);
}
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_370);
lean_ctor_set_tag(x_174, 11);
lean_ctor_set(x_174, 0, x_449);
if (lean_is_scalar(x_19)) {
 x_450 = lean_alloc_ctor(0, 4, 0);
} else {
 x_450 = x_19;
}
lean_ctor_set(x_450, 0, x_445);
lean_ctor_set(x_450, 1, x_391);
lean_ctor_set(x_450, 2, x_174);
lean_ctor_set(x_450, 3, x_447);
if (lean_is_scalar(x_448)) {
 x_451 = lean_alloc_ctor(0, 1, 0);
} else {
 x_451 = x_448;
}
lean_ctor_set(x_451, 0, x_450);
return x_451;
}
else
{
lean_dec(x_445);
lean_dec(x_391);
lean_dec(x_370);
lean_free_object(x_174);
lean_dec(x_19);
return x_446;
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_391);
lean_dec(x_370);
lean_free_object(x_174);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_452 = lean_ctor_get(x_444, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_453 = x_444;
} else {
 lean_dec_ref(x_444);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_455 = lean_ctor_get(x_390, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 x_456 = x_390;
} else {
 lean_dec_ref(x_390);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_455);
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_458 = lean_ctor_get(x_372, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_459 = x_372;
} else {
 lean_dec_ref(x_372);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
return x_460;
}
}
}
case 7:
{
uint8_t x_461; 
lean_free_object(x_174);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_461 = !lean_is_exclusive(x_178);
if (x_461 == 0)
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_462 = lean_ctor_get(x_178, 0);
lean_dec(x_462);
x_463 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_464 = 1;
x_465 = l_Lean_Name_toString(x_154, x_464);
lean_ctor_set_tag(x_178, 3);
lean_ctor_set(x_178, 0, x_465);
x_466 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_178);
x_467 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_468 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
x_469 = l_Lean_MessageData_ofFormat(x_468);
x_470 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_469, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_470;
}
else
{
lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_178);
x_471 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_472 = 1;
x_473 = l_Lean_Name_toString(x_154, x_472);
x_474 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_475 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_475, 0, x_471);
lean_ctor_set(x_475, 1, x_474);
x_476 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_477 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = l_Lean_MessageData_ofFormat(x_477);
x_479 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_478, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_479;
}
}
default: 
{
lean_object* x_480; 
lean_free_object(x_174);
lean_dec(x_178);
lean_dec_ref(x_155);
lean_dec(x_19);
x_480 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_154, x_159, x_3, x_4, x_5);
return x_480;
}
}
}
else
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_174, 0);
lean_inc(x_481);
lean_dec(x_174);
switch (lean_obj_tag(x_481)) {
case 0:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_482 = x_481;
} else {
 lean_dec_ref(x_481);
 x_482 = lean_box(0);
}
x_483 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_484 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_485 = 1;
x_486 = l_Lean_Name_toString(x_154, x_485);
if (lean_is_scalar(x_482)) {
 x_487 = lean_alloc_ctor(3, 1, 0);
} else {
 x_487 = x_482;
 lean_ctor_set_tag(x_487, 3);
}
lean_ctor_set(x_487, 0, x_486);
x_488 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_488, 0, x_484);
lean_ctor_set(x_488, 1, x_487);
x_489 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_490 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = l_Lean_MessageData_ofFormat(x_490);
x_492 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_483, x_491, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_492;
}
case 2:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_493 = x_481;
} else {
 lean_dec_ref(x_481);
 x_493 = lean_box(0);
}
x_494 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_495 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_496 = 1;
x_497 = l_Lean_Name_toString(x_154, x_496);
if (lean_is_scalar(x_493)) {
 x_498 = lean_alloc_ctor(3, 1, 0);
} else {
 x_498 = x_493;
 lean_ctor_set_tag(x_498, 3);
}
lean_ctor_set(x_498, 0, x_497);
x_499 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_499, 0, x_495);
lean_ctor_set(x_499, 1, x_498);
x_500 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_501 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
x_502 = l_Lean_MessageData_ofFormat(x_501);
x_503 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_494, x_502, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_503;
}
case 4:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_504 = x_481;
} else {
 lean_dec_ref(x_481);
 x_504 = lean_box(0);
}
x_505 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_506 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_507 = 1;
x_508 = l_Lean_Name_toString(x_154, x_507);
if (lean_is_scalar(x_504)) {
 x_509 = lean_alloc_ctor(3, 1, 0);
} else {
 x_509 = x_504;
 lean_ctor_set_tag(x_509, 3);
}
lean_ctor_set(x_509, 0, x_508);
x_510 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_510, 0, x_506);
lean_ctor_set(x_510, 1, x_509);
x_511 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_512 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_513 = l_Lean_MessageData_ofFormat(x_512);
x_514 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_505, x_513, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_514;
}
case 5:
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_515 = x_481;
} else {
 lean_dec_ref(x_481);
 x_515 = lean_box(0);
}
x_516 = l_Lean_IR_ToIR_lowerLet___closed__7;
x_517 = l_Lean_IR_ToIR_lowerLet___closed__9;
x_518 = 1;
x_519 = l_Lean_Name_toString(x_154, x_518);
if (lean_is_scalar(x_515)) {
 x_520 = lean_alloc_ctor(3, 1, 0);
} else {
 x_520 = x_515;
 lean_ctor_set_tag(x_520, 3);
}
lean_ctor_set(x_520, 0, x_519);
x_521 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_521, 0, x_517);
lean_ctor_set(x_521, 1, x_520);
x_522 = l_Lean_IR_ToIR_lowerLet___closed__11;
x_523 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
x_524 = l_Lean_MessageData_ofFormat(x_523);
x_525 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_516, x_524, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_525;
}
case 6:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_inc_ref(x_16);
lean_inc(x_15);
lean_dec_ref(x_1);
x_526 = lean_ctor_get(x_481, 0);
lean_inc_ref(x_526);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_527 = x_481;
} else {
 lean_dec_ref(x_481);
 x_527 = lean_box(0);
}
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
x_529 = lean_ctor_get(x_526, 2);
lean_inc(x_529);
x_530 = lean_ctor_get(x_526, 3);
lean_inc(x_530);
lean_dec_ref(x_526);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_528);
x_531 = l_Lean_IR_hasTrivialStructure_x3f(x_528, x_4, x_5);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
lean_dec_ref(x_531);
if (lean_obj_tag(x_532) == 1)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
lean_dec_ref(x_532);
x_534 = lean_st_ref_take(x_3);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
x_536 = lean_ctor_get(x_533, 2);
lean_inc(x_536);
lean_dec(x_533);
x_537 = lean_ctor_get(x_534, 0);
lean_inc_ref(x_537);
x_538 = lean_ctor_get(x_534, 1);
lean_inc_ref(x_538);
x_539 = lean_ctor_get(x_534, 2);
lean_inc(x_539);
x_540 = lean_ctor_get(x_534, 3);
lean_inc_ref(x_540);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 lean_ctor_release(x_534, 2);
 lean_ctor_release(x_534, 3);
 x_541 = x_534;
} else {
 lean_dec_ref(x_534);
 x_541 = lean_box(0);
}
x_542 = lean_box(0);
x_543 = lean_nat_add(x_535, x_536);
lean_dec(x_536);
lean_dec(x_535);
x_544 = lean_array_get(x_542, x_155, x_543);
lean_dec(x_543);
lean_dec_ref(x_155);
x_545 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_IR_ToIR_lowerParam_spec__0___redArg(x_540, x_15, x_544);
if (lean_is_scalar(x_541)) {
 x_546 = lean_alloc_ctor(0, 4, 0);
} else {
 x_546 = x_541;
}
lean_ctor_set(x_546, 0, x_537);
lean_ctor_set(x_546, 1, x_538);
lean_ctor_set(x_546, 2, x_539);
lean_ctor_set(x_546, 3, x_545);
x_547 = lean_st_ref_set(x_3, x_546);
x_548 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
return x_548;
}
else
{
lean_object* x_549; 
lean_dec(x_532);
lean_dec_ref(x_155);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_528);
x_549 = l_Lean_IR_nameToIRType(x_528, x_4, x_5);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; uint8_t x_551; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
lean_dec_ref(x_549);
x_551 = l_Lean_IR_IRType_isScalar(x_550);
if (x_551 == 0)
{
lean_object* x_552; 
lean_dec(x_550);
lean_dec(x_529);
lean_dec(x_527);
lean_inc(x_5);
lean_inc_ref(x_4);
x_552 = l_Lean_IR_getCtorLayout(x_154, x_4, x_5);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 x_554 = x_552;
} else {
 lean_dec_ref(x_552);
 x_554 = lean_box(0);
}
x_558 = lean_ctor_get(x_553, 0);
lean_inc_ref(x_558);
x_559 = lean_ctor_get(x_553, 1);
lean_inc_ref(x_559);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 x_560 = x_553;
} else {
 lean_dec_ref(x_553);
 x_560 = lean_box(0);
}
x_561 = lean_array_get_size(x_159);
x_562 = l_Array_extract___redArg(x_159, x_530, x_561);
lean_dec(x_159);
x_563 = lean_array_get_size(x_562);
x_564 = lean_array_get_size(x_559);
x_565 = lean_nat_dec_eq(x_563, x_564);
if (x_565 == 0)
{
lean_dec_ref(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec_ref(x_558);
lean_dec(x_528);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_557;
}
else
{
if (x_551 == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
lean_dec(x_554);
x_566 = l_Lean_IR_instInhabitedArg_default;
x_567 = lean_unsigned_to_nat(0u);
x_568 = l_Lean_IR_ToIR_lowerLet___closed__12;
x_569 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(x_564, x_559, x_566, x_562, x_567, x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
lean_dec_ref(x_569);
x_571 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec_ref(x_571);
x_585 = lean_st_ref_get(x_5);
x_586 = lean_ctor_get(x_585, 0);
lean_inc_ref(x_586);
lean_dec(x_585);
x_587 = l_Lean_IR_UnboxResult_hasUnboxAttr(x_586, x_528);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec_ref(x_16);
x_588 = l_Lean_IR_CtorInfo_type(x_558);
x_573 = x_588;
x_574 = x_3;
x_575 = x_4;
x_576 = x_5;
x_577 = lean_box(0);
goto block_584;
}
else
{
lean_object* x_589; 
lean_inc(x_5);
lean_inc_ref(x_4);
x_589 = l_Lean_IR_toIRType(x_16, x_4, x_5);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
lean_dec_ref(x_589);
x_573 = x_590;
x_574 = x_3;
x_575 = x_4;
x_576 = x_5;
x_577 = lean_box(0);
goto block_584;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_572);
lean_dec(x_570);
lean_dec_ref(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec_ref(x_558);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_591 = lean_ctor_get(x_589, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_592 = x_589;
} else {
 lean_dec_ref(x_589);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 1, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_591);
return x_593;
}
}
block_584:
{
lean_object* x_578; 
lean_inc(x_572);
lean_inc_ref(x_558);
x_578 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_2, x_558, x_559, x_562, x_572, x_574, x_575, x_576);
lean_dec_ref(x_562);
lean_dec_ref(x_559);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_580 = x_578;
} else {
 lean_dec_ref(x_578);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_560)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_560;
}
lean_ctor_set(x_581, 0, x_558);
lean_ctor_set(x_581, 1, x_570);
if (lean_is_scalar(x_19)) {
 x_582 = lean_alloc_ctor(0, 4, 0);
} else {
 x_582 = x_19;
}
lean_ctor_set(x_582, 0, x_572);
lean_ctor_set(x_582, 1, x_573);
lean_ctor_set(x_582, 2, x_581);
lean_ctor_set(x_582, 3, x_579);
if (lean_is_scalar(x_580)) {
 x_583 = lean_alloc_ctor(0, 1, 0);
} else {
 x_583 = x_580;
}
lean_ctor_set(x_583, 0, x_582);
return x_583;
}
else
{
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_560);
lean_dec_ref(x_558);
lean_dec(x_19);
return x_578;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_570);
lean_dec_ref(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec_ref(x_558);
lean_dec(x_528);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_594 = lean_ctor_get(x_571, 0);
lean_inc(x_594);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_595 = x_571;
} else {
 lean_dec_ref(x_571);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_594);
return x_596;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec_ref(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec_ref(x_558);
lean_dec(x_528);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_597 = lean_ctor_get(x_569, 0);
lean_inc(x_597);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_598 = x_569;
} else {
 lean_dec_ref(x_569);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 1, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_597);
return x_599;
}
}
else
{
lean_dec_ref(x_562);
lean_dec(x_560);
lean_dec_ref(x_559);
lean_dec_ref(x_558);
lean_dec(x_528);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
goto block_557;
}
}
block_557:
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_box(12);
if (lean_is_scalar(x_554)) {
 x_556 = lean_alloc_ctor(0, 1, 0);
} else {
 x_556 = x_554;
}
lean_ctor_set(x_556, 0, x_555);
return x_556;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_dec(x_530);
lean_dec(x_528);
lean_dec(x_159);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_600 = lean_ctor_get(x_552, 0);
lean_inc(x_600);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 x_601 = x_552;
} else {
 lean_dec_ref(x_552);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 1, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_600);
return x_602;
}
}
else
{
lean_object* x_603; 
lean_dec(x_530);
lean_dec(x_528);
lean_dec(x_159);
lean_dec(x_154);
lean_dec_ref(x_16);
x_603 = l_Lean_IR_ToIR_bindVar___redArg(x_15, x_3);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
lean_dec_ref(x_603);
x_605 = l_Lean_IR_ToIR_lowerCode(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 x_607 = x_605;
} else {
 lean_dec_ref(x_605);
 x_607 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_608 = lean_alloc_ctor(0, 1, 0);
} else {
 x_608 = x_527;
 lean_ctor_set_tag(x_608, 0);
}
lean_ctor_set(x_608, 0, x_529);
x_609 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_609, 0, x_608);
if (lean_is_scalar(x_19)) {
 x_610 = lean_alloc_ctor(0, 4, 0);
} else {
 x_610 = x_19;
}
lean_ctor_set(x_610, 0, x_604);
lean_ctor_set(x_610, 1, x_550);
lean_ctor_set(x_610, 2, x_609);
lean_ctor_set(x_610, 3, x_606);
if (lean_is_scalar(x_607)) {
 x_611 = lean_alloc_ctor(0, 1, 0);
} else {
 x_611 = x_607;
}
lean_ctor_set(x_611, 0, x_610);
return x_611;
}
else
{
lean_dec(x_604);
lean_dec(x_550);
lean_dec(x_529);
lean_dec(x_527);
lean_dec(x_19);
return x_605;
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_550);
lean_dec(x_529);
lean_dec(x_527);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_612 = lean_ctor_get(x_603, 0);
lean_inc(x_612);
if (lean_is_exclusive(x_603)) {
 lean_ctor_release(x_603, 0);
 x_613 = x_603;
} else {
 lean_dec_ref(x_603);
 x_613 = lean_box(0);
}
if (lean_is_scalar(x_613)) {
 x_614 = lean_alloc_ctor(1, 1, 0);
} else {
 x_614 = x_613;
}
lean_ctor_set(x_614, 0, x_612);
return x_614;
}
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_615 = lean_ctor_get(x_549, 0);
lean_inc(x_615);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 x_616 = x_549;
} else {
 lean_dec_ref(x_549);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 1, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_615);
return x_617;
}
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_618 = lean_ctor_get(x_531, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 x_619 = x_531;
} else {
 lean_dec_ref(x_531);
 x_619 = lean_box(0);
}
if (lean_is_scalar(x_619)) {
 x_620 = lean_alloc_ctor(1, 1, 0);
} else {
 x_620 = x_619;
}
lean_ctor_set(x_620, 0, x_618);
return x_620;
}
}
case 7:
{
lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_19);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_621 = x_481;
} else {
 lean_dec_ref(x_481);
 x_621 = lean_box(0);
}
x_622 = l_Lean_IR_ToIR_lowerLet___closed__14;
x_623 = 1;
x_624 = l_Lean_Name_toString(x_154, x_623);
if (lean_is_scalar(x_621)) {
 x_625 = lean_alloc_ctor(3, 1, 0);
} else {
 x_625 = x_621;
 lean_ctor_set_tag(x_625, 3);
}
lean_ctor_set(x_625, 0, x_624);
x_626 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_626, 0, x_622);
lean_ctor_set(x_626, 1, x_625);
x_627 = l_Lean_IR_ToIR_lowerLet___closed__16;
x_628 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
x_629 = l_Lean_MessageData_ofFormat(x_628);
x_630 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_629, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_630;
}
default: 
{
lean_object* x_631; 
lean_dec(x_481);
lean_dec_ref(x_155);
lean_dec(x_19);
x_631 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_154, x_159, x_3, x_4, x_5);
return x_631;
}
}
}
}
}
}
else
{
uint8_t x_632; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_632 = !lean_is_exclusive(x_166);
if (x_632 == 0)
{
return x_166;
}
else
{
lean_object* x_633; lean_object* x_634; 
x_633 = lean_ctor_get(x_166, 0);
lean_inc(x_633);
lean_dec(x_166);
x_634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_634, 0, x_633);
return x_634;
}
}
}
}
else
{
uint8_t x_635; 
lean_dec(x_159);
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_635 = !lean_is_exclusive(x_160);
if (x_635 == 0)
{
return x_160;
}
else
{
lean_object* x_636; lean_object* x_637; 
x_636 = lean_ctor_get(x_160, 0);
lean_inc(x_636);
lean_dec(x_160);
x_637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_637, 0, x_636);
return x_637;
}
}
}
else
{
uint8_t x_638; 
lean_dec_ref(x_155);
lean_dec(x_154);
lean_dec(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_638 = !lean_is_exclusive(x_158);
if (x_638 == 0)
{
return x_158;
}
else
{
lean_object* x_639; lean_object* x_640; 
x_639 = lean_ctor_get(x_158, 0);
lean_inc(x_639);
lean_dec(x_158);
x_640 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_640, 0, x_639);
return x_640;
}
}
}
default: 
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_19);
x_641 = lean_ctor_get(x_21, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_642);
lean_dec_ref(x_21);
x_643 = l_Lean_IR_ToIR_getFVarValue___redArg(x_641, x_3);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec_ref(x_643);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; size_t x_646; size_t x_647; lean_object* x_648; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
lean_dec_ref(x_644);
x_646 = lean_array_size(x_642);
x_647 = 0;
x_648 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_646, x_647, x_642, x_3);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
lean_dec_ref(x_648);
x_650 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_645, x_649, x_3, x_4, x_5);
return x_650;
}
else
{
uint8_t x_651; 
lean_dec(x_645);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_651 = !lean_is_exclusive(x_648);
if (x_651 == 0)
{
return x_648;
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_648, 0);
lean_inc(x_652);
lean_dec(x_648);
x_653 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_653, 0, x_652);
return x_653;
}
}
}
else
{
lean_object* x_654; 
lean_dec_ref(x_642);
x_654 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_654;
}
}
else
{
uint8_t x_655; 
lean_dec_ref(x_642);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_655 = !lean_is_exclusive(x_643);
if (x_655 == 0)
{
return x_643;
}
else
{
lean_object* x_656; lean_object* x_657; 
x_656 = lean_ctor_get(x_643, 0);
lean_inc(x_656);
lean_dec(x_643);
x_657 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_657, 0, x_656);
return x_657;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_IR_ToIR_lowerLet___closed__2;
x_12 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_11, x_7, x_8, x_9);
return x_12;
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("all local functions should be λ-lifted", 39, 38);
return x_1;
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
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__1;
x_2 = lean_unsigned_to_nat(15u);
x_3 = lean_unsigned_to_nat(168u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: cases.alts.size == 1\n      ", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__3;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(147u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ctorName == info.ctorName\n      ", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__5;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(149u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: info.fieldIdx < ps.size\n      ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__7;
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_unsigned_to_nat(150u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_2 = lean_unsigned_to_nat(49u);
x_3 = lean_unsigned_to_nat(148u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mismatched fields and params", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerAlt.loop", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(331u);
x_4 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_51; lean_object* x_58; uint8_t x_59; 
x_58 = lean_array_get_size(x_4);
x_59 = lean_nat_dec_lt(x_6, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_51 = x_60;
goto block_57;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_array_fget_borrowed(x_4, x_6);
lean_inc(x_61);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_51 = x_62;
goto block_57;
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3;
x_16 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_15, x_11, x_12, x_13);
return x_16;
}
block_50:
{
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9);
return x_20;
}
else
{
lean_dec(x_19);
lean_dec_ref(x_2);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = lean_box(0);
goto block_17;
}
}
else
{
if (lean_obj_tag(x_19) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec_ref(x_19);
lean_inc(x_1);
x_23 = l_Lean_IR_ToIR_lowerProj(x_1, x_3, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_24);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_IR_ToIR_bindVar___redArg(x_27, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_6, x_30);
lean_dec(x_6);
x_32 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_31, x_7, x_8, x_9);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_26);
lean_ctor_set(x_35, 3, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_25);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_26);
lean_dec(x_25);
return x_32;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_28, 0);
lean_inc(x_40);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_23);
x_42 = lean_ctor_get(x_21, 0);
lean_inc(x_42);
lean_dec(x_21);
x_43 = l_Lean_IR_ToIR_bindErased___redArg(x_42, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_6 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
else
{
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_6);
lean_dec_ref(x_2);
lean_dec(x_1);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = lean_box(0);
goto block_17;
}
}
}
block_57:
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_array_get_size(x_5);
x_53 = lean_nat_dec_lt(x_6, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_18 = x_51;
x_19 = x_54;
goto block_50;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_array_fget_borrowed(x_5, x_6);
lean_inc(x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_18 = x_51;
x_19 = x_56;
goto block_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc_ref(x_9);
lean_dec_ref(x_2);
lean_inc(x_5);
lean_inc_ref(x_4);
x_10 = l_Lean_IR_getCtorLayout(x_7, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_13, x_8, x_14, x_15, x_3, x_4, x_5);
lean_dec_ref(x_14);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_11, 1, x_18);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_11, 1, x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_11);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_11);
lean_dec_ref(x_13);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_24, x_8, x_25, x_26, x_3, x_4, x_5);
lean_dec_ref(x_25);
lean_dec_ref(x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_28);
if (lean_is_scalar(x_29)) {
 x_31 = lean_alloc_ctor(0, 1, 0);
} else {
 x_31 = x_29;
}
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_24);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_33 = x_27;
} else {
 lean_dec_ref(x_27);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = l_Lean_IR_ToIR_lowerCode(x_39, x_3, x_4, x_5);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set(x_40, 0, x_2);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_2, 0, x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_2);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_free_object(x_2);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
lean_dec(x_2);
x_49 = l_Lean_IR_ToIR_lowerCode(x_48, x_3, x_4, x_5);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_51 = x_49;
} else {
 lean_dec_ref(x_49);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 1, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_4, x_3);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_IR_ToIR_lowerAlt(x_1, x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_18 = lean_array_uset(x_15, x_3, x_13);
x_3 = x_17;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerCode___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_IR_ToIR_lowerCode___closed__9;
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(160u);
x_4 = l_Lean_IR_ToIR_lowerCode___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_IR_ToIR_lowerLet(x_6, x_7, x_2, x_3, x_4);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_lowerCode___closed__2;
x_10 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_9, x_2, x_3, x_4);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 4);
lean_inc_ref(x_15);
lean_dec_ref(x_11);
x_16 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_13, x_2);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_size(x_14);
x_19 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(x_18, x_19, x_14, x_2, x_3, x_4);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
x_22 = l_Lean_IR_ToIR_lowerCode(x_15, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l_Lean_IR_ToIR_lowerCode(x_12, x_2, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_23);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
return x_24;
}
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_22;
}
}
else
{
uint8_t x_31; 
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_12);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_16, 0);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
case 3:
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_37 = !lean_is_exclusive(x_1);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_38, x_2);
lean_dec(x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_size(x_39);
x_43 = 0;
x_44 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_42, x_43, x_39, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_46);
lean_ctor_set(x_1, 0, x_41);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
lean_ctor_set_tag(x_1, 11);
lean_ctor_set(x_1, 1, x_47);
lean_ctor_set(x_1, 0, x_41);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_1);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_41);
lean_free_object(x_1);
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_free_object(x_1);
lean_dec_ref(x_39);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_1);
x_57 = l_Lean_IR_ToIR_getJoinPointValue___redArg(x_55, x_2);
lean_dec(x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_59 = lean_array_size(x_56);
x_60 = 0;
x_61 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_59, x_60, x_56, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_58);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec_ref(x_56);
lean_dec(x_2);
x_69 = lean_ctor_get(x_57, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_70 = x_57;
} else {
 lean_dec_ref(x_57);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
return x_71;
}
}
}
case 4:
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_72);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_ctor_get(x_72, 2);
x_76 = lean_ctor_get(x_72, 3);
x_77 = lean_ctor_get(x_72, 1);
lean_dec(x_77);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_74);
x_78 = l_Lean_IR_hasTrivialStructure_x3f(x_74, x_3, x_4);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
if (lean_obj_tag(x_79) == 1)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_free_object(x_72);
lean_dec(x_74);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec_ref(x_79);
x_81 = lean_array_get_size(x_76);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_80);
lean_dec_ref(x_76);
lean_dec(x_75);
x_84 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_85 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_84, x_2, x_3, x_4);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_array_get(x_86, x_76, x_87);
lean_dec_ref(x_76);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_90);
x_91 = lean_ctor_get(x_88, 2);
lean_inc_ref(x_91);
lean_dec_ref(x_88);
x_92 = lean_ctor_get(x_80, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_80, 2);
lean_inc(x_93);
lean_dec(x_80);
x_94 = lean_name_eq(x_89, x_92);
lean_dec(x_92);
lean_dec(x_89);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_93);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec(x_75);
x_95 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_96 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_95, x_2, x_3, x_4);
return x_96;
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_array_get_size(x_90);
x_98 = lean_nat_dec_lt(x_93, x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_93);
lean_dec_ref(x_91);
lean_dec_ref(x_90);
lean_dec(x_75);
x_99 = l_Lean_IR_ToIR_lowerCode___closed__8;
x_100 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_99, x_2, x_3, x_4);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_box(0);
x_102 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(x_97, x_90, x_93, x_101, x_75, x_87, x_101, x_2);
lean_dec(x_93);
lean_dec_ref(x_90);
if (lean_obj_tag(x_102) == 0)
{
lean_dec_ref(x_102);
x_1 = x_91;
goto _start;
}
else
{
uint8_t x_104; 
lean_dec_ref(x_91);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
return x_102;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
lean_dec(x_80);
lean_dec(x_75);
x_107 = l_Lean_IR_ToIR_lowerCode___closed__10;
x_108 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_107, x_2, x_3, x_4);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_79);
x_109 = l_Lean_IR_ToIR_getFVarValue___redArg(x_75, x_2);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_74);
x_112 = l_Lean_IR_nameToIRType(x_74, x_3, x_4);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec_ref(x_112);
x_114 = lean_array_size(x_76);
x_115 = 0;
lean_inc(x_111);
x_116 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5(x_111, x_114, x_115, x_76, x_2, x_3, x_4);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_ctor_set_tag(x_72, 9);
lean_ctor_set(x_72, 3, x_118);
lean_ctor_set(x_72, 2, x_113);
lean_ctor_set(x_72, 1, x_111);
lean_ctor_set(x_116, 0, x_72);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
lean_ctor_set_tag(x_72, 9);
lean_ctor_set(x_72, 3, x_119);
lean_ctor_set(x_72, 2, x_113);
lean_ctor_set(x_72, 1, x_111);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_72);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_113);
lean_dec(x_111);
lean_free_object(x_72);
lean_dec(x_74);
x_121 = !lean_is_exclusive(x_116);
if (x_121 == 0)
{
return x_116;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_111);
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_74);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_112);
if (x_124 == 0)
{
return x_112;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_112, 0);
lean_inc(x_125);
lean_dec(x_112);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_110);
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_74);
x_127 = l_Lean_IR_ToIR_lowerCode___closed__11;
x_128 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_127, x_2, x_3, x_4);
return x_128;
}
}
else
{
uint8_t x_129; 
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_74);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_109);
if (x_129 == 0)
{
return x_109;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_109, 0);
lean_inc(x_130);
lean_dec(x_109);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
}
else
{
uint8_t x_132; 
lean_free_object(x_72);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_78);
if (x_132 == 0)
{
return x_78;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_78, 0);
lean_inc(x_133);
lean_dec(x_78);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_72, 0);
x_136 = lean_ctor_get(x_72, 2);
x_137 = lean_ctor_get(x_72, 3);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_72);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_135);
x_138 = l_Lean_IR_hasTrivialStructure_x3f(x_135, x_3, x_4);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec_ref(x_138);
if (lean_obj_tag(x_139) == 1)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; 
lean_dec(x_135);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec_ref(x_139);
x_141 = lean_array_get_size(x_137);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_dec_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_140);
lean_dec_ref(x_137);
lean_dec(x_136);
x_144 = l_Lean_IR_ToIR_lowerCode___closed__4;
x_145 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_144, x_2, x_3, x_4);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1;
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_array_get(x_146, x_137, x_147);
lean_dec_ref(x_137);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc_ref(x_150);
x_151 = lean_ctor_get(x_148, 2);
lean_inc_ref(x_151);
lean_dec_ref(x_148);
x_152 = lean_ctor_get(x_140, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_140, 2);
lean_inc(x_153);
lean_dec(x_140);
x_154 = lean_name_eq(x_149, x_152);
lean_dec(x_152);
lean_dec(x_149);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_153);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_136);
x_155 = l_Lean_IR_ToIR_lowerCode___closed__6;
x_156 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_155, x_2, x_3, x_4);
return x_156;
}
else
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_array_get_size(x_150);
x_158 = lean_nat_dec_lt(x_153, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_153);
lean_dec_ref(x_151);
lean_dec_ref(x_150);
lean_dec(x_136);
x_159 = l_Lean_IR_ToIR_lowerCode___closed__8;
x_160 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_159, x_2, x_3, x_4);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_box(0);
x_162 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(x_157, x_150, x_153, x_161, x_136, x_147, x_161, x_2);
lean_dec(x_153);
lean_dec_ref(x_150);
if (lean_obj_tag(x_162) == 0)
{
lean_dec_ref(x_162);
x_1 = x_151;
goto _start;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_151);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
return x_166;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_148);
lean_dec(x_140);
lean_dec(x_136);
x_167 = l_Lean_IR_ToIR_lowerCode___closed__10;
x_168 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_167, x_2, x_3, x_4);
return x_168;
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_139);
x_169 = l_Lean_IR_ToIR_getFVarValue___redArg(x_136, x_2);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_135);
x_172 = l_Lean_IR_nameToIRType(x_135, x_3, x_4);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = lean_array_size(x_137);
x_175 = 0;
lean_inc(x_171);
x_176 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5(x_171, x_174, x_175, x_137, x_2, x_3, x_4);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_178 = x_176;
} else {
 lean_dec_ref(x_176);
 x_178 = lean_box(0);
}
x_179 = lean_alloc_ctor(9, 4, 0);
lean_ctor_set(x_179, 0, x_135);
lean_ctor_set(x_179, 1, x_171);
lean_ctor_set(x_179, 2, x_173);
lean_ctor_set(x_179, 3, x_177);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 1, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_135);
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_171);
lean_dec_ref(x_137);
lean_dec(x_135);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_172, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_185 = x_172;
} else {
 lean_dec_ref(x_172);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_170);
lean_dec_ref(x_137);
lean_dec(x_135);
x_187 = l_Lean_IR_ToIR_lowerCode___closed__11;
x_188 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop_spec__0(x_187, x_2, x_3, x_4);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_137);
lean_dec(x_135);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_189 = lean_ctor_get(x_169, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_190 = x_169;
} else {
 lean_dec_ref(x_169);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_192 = lean_ctor_get(x_138, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 x_193 = x_138;
} else {
 lean_dec_ref(x_138);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
}
case 5:
{
uint8_t x_195; 
lean_dec(x_4);
lean_dec_ref(x_3);
x_195 = !lean_is_exclusive(x_1);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_1, 0);
x_197 = l_Lean_IR_ToIR_getFVarValue___redArg(x_196, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_197) == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_197, 0);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_199);
lean_ctor_set(x_197, 0, x_1);
return x_197;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
lean_dec(x_197);
lean_ctor_set_tag(x_1, 10);
lean_ctor_set(x_1, 0, x_200);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_1);
return x_201;
}
}
else
{
uint8_t x_202; 
lean_free_object(x_1);
x_202 = !lean_is_exclusive(x_197);
if (x_202 == 0)
{
return x_197;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_197, 0);
lean_inc(x_203);
lean_dec(x_197);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
}
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_1, 0);
lean_inc(x_205);
lean_dec(x_1);
x_206 = l_Lean_IR_ToIR_getFVarValue___redArg(x_205, x_2);
lean_dec(x_2);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(x_209, 0, x_207);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_206, 0);
lean_inc(x_211);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_212 = x_206;
} else {
 lean_dec_ref(x_206);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_211);
return x_213;
}
}
}
default: 
{
uint8_t x_214; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_214 = !lean_is_exclusive(x_1);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_1, 0);
lean_dec(x_215);
x_216 = lean_box(12);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_216);
return x_1;
}
else
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_1);
x_217 = lean_box(12);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
return x_218;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_6, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_13 = l_Lean_IR_ToIR_lowerCode(x_1, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fget_borrowed(x_4, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
x_16 = lean_box(0);
x_17 = lean_array_get_borrowed(x_16, x_3, x_6);
switch (lean_obj_tag(x_17)) {
case 1:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_6 = x_19;
goto _start;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_6, x_22);
lean_dec(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_24 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_2, 4);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 3);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_2, 0);
lean_dec(x_31);
lean_inc(x_15);
lean_inc(x_21);
lean_ctor_set_tag(x_2, 4);
lean_ctor_set(x_2, 4, x_27);
lean_ctor_set(x_2, 3, x_15);
lean_ctor_set(x_2, 2, x_21);
lean_ctor_set(x_2, 0, x_5);
lean_ctor_set(x_24, 0, x_2);
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_21);
x_34 = lean_alloc_ctor(4, 5, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_15);
lean_ctor_set(x_34, 4, x_32);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 x_37 = x_2;
} else {
 lean_dec_ref(x_2);
 x_37 = lean_box(0);
}
lean_inc(x_15);
lean_inc(x_21);
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(4, 5, 0);
} else {
 x_38 = x_37;
 lean_ctor_set_tag(x_38, 4);
}
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_21);
lean_ctor_set(x_38, 3, x_15);
lean_ctor_set(x_38, 4, x_35);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_2);
return x_24;
}
}
case 3:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_17, 1);
x_41 = lean_ctor_get(x_17, 2);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_6, x_42);
lean_dec(x_6);
lean_inc(x_5);
lean_inc_ref(x_2);
x_44 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_43, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_2, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 3);
lean_inc(x_49);
lean_dec_ref(x_2);
x_50 = lean_nat_add(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
lean_inc(x_41);
lean_inc(x_15);
lean_inc(x_40);
x_51 = lean_alloc_ctor(5, 7, 0);
lean_ctor_set(x_51, 0, x_5);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_40);
lean_ctor_set(x_51, 4, x_15);
lean_ctor_set(x_51, 5, x_41);
lean_ctor_set(x_51, 6, x_46);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_44, 0);
lean_inc(x_52);
lean_dec(x_44);
x_53 = lean_ctor_get(x_2, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_2, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_55);
lean_dec_ref(x_2);
x_56 = lean_nat_add(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
lean_inc(x_41);
lean_inc(x_15);
lean_inc(x_40);
x_57 = lean_alloc_ctor(5, 7, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_40);
lean_ctor_set(x_57, 4, x_15);
lean_ctor_set(x_57, 5, x_41);
lean_ctor_set(x_57, 6, x_52);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_2);
return x_44;
}
}
default: 
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_add(x_6, x_59);
lean_dec(x_6);
x_6 = x_60;
goto _start;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_6, x_62);
lean_dec(x_6);
x_6 = x_63;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkPap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__5(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkFap(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkAp(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerAlt(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkOverApplication(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerCode(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerLet(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___redArg(x_1, x_2, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkErased(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_lowerNonObjectFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___redArg(x_1, x_2, x_3, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__3(x_8, x_9, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerCode_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___redArg(x_2, x_3, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___redArg(x_1, x_2, x_3, x_4, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_WellFounded_opaqueFix_u2083___at___00Lean_IR_ToIR_lowerLet_spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_8, x_3, x_4);
lean_dec_ref(x_9);
x_10 = l_Lean_IR_ToIR_lowerCode(x_2, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerLet_mkVar(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerResultType.resultTypeForArity", 47, 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid arity", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(348u);
x_4 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0;
x_5 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lcErased", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
switch (lean_obj_tag(x_1)) {
case 7:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
case 4:
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_12, 1);
x_15 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3;
x_16 = lean_string_dec_eq(x_14, x_15);
if (x_16 == 0)
{
goto block_5;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5;
return x_17;
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
lean_inc_ref(x_1);
return x_1;
}
block_5:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2;
x_4 = l_panic___at___00__private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity_spec__0(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_7 = l_Lean_IR_toIRType(x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType___redArg(x_1, x_2, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerResultType(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Error while compiling function '", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerDecl___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': @[tagged_return] is only valid for extern declarations", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerDecl___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@[tagged_return] on function '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerDecl___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' with scalar return type ", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_ToIR_lowerDecl___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_ToIR_lowerDecl___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; size_t x_21; size_t x_22; lean_object* x_23; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_21 = lean_array_size(x_12);
x_22 = 0;
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_12);
x_23 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_IR_ToIR_lowerCode_spec__2(x_21, x_22, x_12, x_2, x_3, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_array_get_size(x_12);
lean_dec_ref(x_12);
lean_inc(x_4);
lean_inc_ref(x_3);
x_26 = l_Lean_IR_ToIR_lowerResultType___redArg(x_11, x_25, x_3, x_4);
lean_dec_ref(x_11);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_st_ref_get(x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = l_Lean_IR_ToIR_taggedReturnAttr;
lean_inc(x_10);
x_32 = l_Lean_TagAttribute_hasTag(x_31, x_30, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
x_33 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_33);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_34 = x_13;
} else {
 lean_dec_ref(x_13);
 x_34 = lean_box(0);
}
if (x_32 == 0)
{
x_35 = x_2;
x_36 = x_3;
x_37 = x_4;
x_38 = lean_box(0);
goto block_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_34);
lean_dec_ref(x_33);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_2);
x_54 = l_Lean_IR_ToIR_lowerDecl___closed__1;
x_55 = l_Lean_MessageData_ofName(x_10);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_IR_ToIR_lowerDecl___closed__3;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_58, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
block_53:
{
lean_object* x_39; 
x_39 = l_Lean_IR_ToIR_lowerCode(x_33, x_35, x_36, x_37);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_10);
lean_ctor_set(x_43, 1, x_24);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_41);
lean_ctor_set(x_43, 4, x_42);
if (lean_is_scalar(x_34)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_34;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_24);
lean_ctor_set(x_47, 2, x_27);
lean_ctor_set(x_47, 3, x_45);
lean_ctor_set(x_47, 4, x_46);
if (lean_is_scalar(x_34)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_34;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_10);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
lean_dec(x_39);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_64 = x_13;
} else {
 lean_dec_ref(x_13);
 x_64 = lean_box(0);
}
if (x_32 == 0)
{
lean_dec_ref(x_3);
x_65 = x_27;
x_66 = x_4;
x_67 = lean_box(0);
goto block_76;
}
else
{
uint8_t x_77; 
x_77 = l_Lean_IR_IRType_isScalar(x_27);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_27);
lean_dec_ref(x_3);
x_78 = lean_box(12);
x_65 = x_78;
x_66 = x_4;
x_67 = lean_box(0);
goto block_76;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_28);
lean_dec(x_24);
x_79 = l_Lean_IR_ToIR_lowerDecl___closed__5;
x_80 = l_Lean_MessageData_ofName(x_10);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_IR_ToIR_lowerDecl___closed__7;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_IR_instToFormatIRType___private__1(x_27);
x_85 = l_Lean_MessageData_ofFormat(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at___00Lean_IR_ToIR_lowerLet_spec__10___redArg(x_86, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
return x_87;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
block_76:
{
uint8_t x_68; 
x_68 = l_List_isEmpty___redArg(x_63);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
x_69 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_69, 0, x_10);
lean_ctor_set(x_69, 1, x_24);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_63);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_69);
if (lean_is_scalar(x_28)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_28;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_28);
lean_inc(x_65);
lean_inc(x_24);
lean_inc(x_10);
x_72 = l_Lean_IR_mkDummyExternDecl(x_10, x_24, x_65);
x_73 = l_Lean_IR_ToIR_addDecl___redArg(x_72, x_66);
lean_dec_ref(x_73);
x_74 = l_Array_isEmpty___redArg(x_24);
lean_dec(x_24);
if (x_74 == 0)
{
x_14 = x_66;
x_15 = lean_box(0);
x_16 = x_65;
x_17 = x_74;
goto block_20;
}
else
{
uint8_t x_75; 
x_75 = l_Lean_IR_IRType_isStruct(x_65);
x_14 = x_66;
x_15 = lean_box(0);
x_16 = x_65;
x_17 = x_75;
goto block_20;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_24);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_26);
if (x_91 == 0)
{
return x_26;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_26, 0);
lean_inc(x_92);
lean_dec(x_26);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_23);
if (x_94 == 0)
{
return x_23;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_23, 0);
lean_inc(x_95);
lean_dec(x_23);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
block_20:
{
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
x_6 = lean_box(0);
goto block_9;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_IR_ExplicitBoxing_boxedConstDecl(x_10, x_16);
x_19 = l_Lean_IR_ToIR_addDecl___redArg(x_18, x_14);
lean_dec(x_14);
lean_dec_ref(x_19);
x_6 = lean_box(0);
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerDecl(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_5);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl___boxed), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_array_push(x_4, x_19);
x_14 = x_20;
goto block_18;
}
else
{
lean_dec(x_13);
x_14 = x_4;
goto block_18;
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_14;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_10;
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
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; 
x_5 = l_Lean_IR_toIR___closed__0;
x_6 = lean_array_size(x_1);
x_7 = 0;
x_8 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_IR_toIR_spec__0(x_1, x_6, x_7, x_5, x_2, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_ToIRType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_UnboxResult(uint8_t builtin);
lean_object* initialize_Lean_Compiler_IR_Boxing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_ToIRType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_UnboxResult(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Boxing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__0_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__1_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__2_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__3_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__4_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__5_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__6_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__7_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_ = _init_l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_IR_ToIR_initFn___closed__8_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_IR_ToIR_initFn_00___x40_Lean_Compiler_IR_ToIR_1721792695____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_ToIR_taggedReturnAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr);
lean_dec_ref(res);
}l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1___closed__0);
if (builtin) {res = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__0);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__1);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__2);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__3);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__4);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__5);
l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6 = _init_l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3___closed__6);
if (builtin) {res = l_Lean_IR_ToIR_taggedReturnAttr___regBuiltin_Lean_IR_ToIR_taggedReturnAttr_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__0);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__1);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__2);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__3);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__4);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__5);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__6);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__7);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__8);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__9);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__10);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__11);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12 = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse___closed__12);
l_Lean_IR_ToIR_instMonadFVarSubstMFalse = _init_l_Lean_IR_ToIR_instMonadFVarSubstMFalse();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstMFalse);
l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0 = _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstStateM___closed__0);
l_Lean_IR_ToIR_instMonadFVarSubstStateM = _init_l_Lean_IR_ToIR_instMonadFVarSubstStateM();
lean_mark_persistent(l_Lean_IR_ToIR_instMonadFVarSubstStateM);
l_Lean_IR_ToIR_M_run___redArg___closed__0 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__0);
l_Lean_IR_ToIR_M_run___redArg___closed__1 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__1);
l_Lean_IR_ToIR_M_run___redArg___closed__2 = _init_l_Lean_IR_ToIR_M_run___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_M_run___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__0);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__1);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__2);
l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3 = _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3();
lean_mark_persistent(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Lean_IR_ToIR_getFVarValue_spec__0_spec__0___redArg___closed__3);
l_Lean_IR_ToIR_addDecl___redArg___closed__0 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__0);
l_Lean_IR_ToIR_addDecl___redArg___closed__1 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__1);
l_Lean_IR_ToIR_addDecl___redArg___closed__2 = _init_l_Lean_IR_ToIR_addDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_addDecl___redArg___closed__2);
l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0 = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj_default___closed__0);
l_Lean_IR_ToIR_instInhabitedTranslatedProj_default = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj_default();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj_default);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
l_Lean_IR_ToIR_lowerProj___closed__0 = _init_l_Lean_IR_ToIR_lowerProj___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__0);
l_Lean_IR_ToIR_lowerProj___closed__1 = _init_l_Lean_IR_ToIR_lowerProj___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerProj___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__0);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__1);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__2);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__3);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__4);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__5);
l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6 = _init_l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6();
lean_mark_persistent(l_Lean_addMessageContextPartial___at___00Lean_throwNamedError___at___00Lean_IR_ToIR_lowerLet_spec__8_spec__16___closed__6);
l_Lean_IR_ToIR_lowerLet___closed__1 = _init_l_Lean_IR_ToIR_lowerLet___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__1);
l_Lean_IR_ToIR_lowerLet___closed__0 = _init_l_Lean_IR_ToIR_lowerLet___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__0);
l_Lean_IR_ToIR_lowerLet___closed__2 = _init_l_Lean_IR_ToIR_lowerLet___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__2);
l_Lean_IR_ToIR_lowerLet___closed__3 = _init_l_Lean_IR_ToIR_lowerLet___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__3);
l_Lean_IR_ToIR_lowerLet___closed__4 = _init_l_Lean_IR_ToIR_lowerLet___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__4);
l_Lean_IR_ToIR_lowerLet___closed__6 = _init_l_Lean_IR_ToIR_lowerLet___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__6);
l_Lean_IR_ToIR_lowerLet___closed__5 = _init_l_Lean_IR_ToIR_lowerLet___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerLet___closed__5);
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
l_Lean_IR_ToIR_lowerCode___closed__1 = _init_l_Lean_IR_ToIR_lowerCode___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__1);
l_Lean_IR_ToIR_lowerCode___closed__0 = _init_l_Lean_IR_ToIR_lowerCode___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__0);
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
l_Lean_IR_ToIR_lowerCode___closed__8 = _init_l_Lean_IR_ToIR_lowerCode___closed__8();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__8);
l_Lean_IR_ToIR_lowerCode___closed__9 = _init_l_Lean_IR_ToIR_lowerCode___closed__9();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__9);
l_Lean_IR_ToIR_lowerCode___closed__10 = _init_l_Lean_IR_ToIR_lowerCode___closed__10();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__10);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__1);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerAlt_loop___closed__3);
l_Lean_IR_ToIR_lowerCode___closed__11 = _init_l_Lean_IR_ToIR_lowerCode___closed__11();
lean_mark_persistent(l_Lean_IR_ToIR_lowerCode___closed__11);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__0);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__1);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__2);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__3);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__4);
l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5 = _init_l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_IR_ToIR_0__Lean_IR_ToIR_lowerResultType_resultTypeForArity___closed__5);
l_Lean_IR_ToIR_lowerDecl___closed__0 = _init_l_Lean_IR_ToIR_lowerDecl___closed__0();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__0);
l_Lean_IR_ToIR_lowerDecl___closed__1 = _init_l_Lean_IR_ToIR_lowerDecl___closed__1();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__1);
l_Lean_IR_ToIR_lowerDecl___closed__2 = _init_l_Lean_IR_ToIR_lowerDecl___closed__2();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__2);
l_Lean_IR_ToIR_lowerDecl___closed__3 = _init_l_Lean_IR_ToIR_lowerDecl___closed__3();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__3);
l_Lean_IR_ToIR_lowerDecl___closed__4 = _init_l_Lean_IR_ToIR_lowerDecl___closed__4();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__4);
l_Lean_IR_ToIR_lowerDecl___closed__5 = _init_l_Lean_IR_ToIR_lowerDecl___closed__5();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__5);
l_Lean_IR_ToIR_lowerDecl___closed__6 = _init_l_Lean_IR_ToIR_lowerDecl___closed__6();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__6);
l_Lean_IR_ToIR_lowerDecl___closed__7 = _init_l_Lean_IR_ToIR_lowerDecl___closed__7();
lean_mark_persistent(l_Lean_IR_ToIR_lowerDecl___closed__7);
l_Lean_IR_toIR___closed__0 = _init_l_Lean_IR_toIR___closed__0();
lean_mark_persistent(l_Lean_IR_toIR___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
