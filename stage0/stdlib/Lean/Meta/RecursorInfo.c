// Lean compiler output
// Module: Lean.Meta.RecursorInfo
// Imports: Init Lean.AuxRecursor Lean.Util.FindExpr Lean.Meta.ExprDefEq
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
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__7;
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___boxed(lean_object*);
lean_object* l_Lean_Meta_recursorAttribute;
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix___closed__1;
lean_object* l_Lean_Meta_binductionOnSuffix;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1;
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4;
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__5(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__4;
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__14;
lean_object* l_Lean_Meta_recOnSuffix;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__5;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfoRec___rarg___lambda__1___closed__3;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
lean_object* l_List_range(lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__5;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
lean_object* l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
extern lean_object* l_Lean_auxRecExt;
extern lean_object* l_Lean_Meta_State_inhabited___closed__7;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__8;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10;
lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__13;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1;
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__1;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object**);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1;
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8;
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkBInductionOnFor(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7___boxed(lean_object*);
lean_object* l_Array_back___at___private_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4;
lean_object* l_Lean_Meta_RecursorInfo_HasToString(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18;
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_Lean_Meta_mkRecOnFor(lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__1;
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__2;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__9;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__3(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__4;
lean_object* l_Lean_Meta_getMajorPos_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
extern lean_object* l_Lean_Format_be___main___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__11;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__1(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__12;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8;
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__16;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(uint8_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object**);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__10;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__1;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_binductionOnSuffix___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfoInduct___rarg___lambda__1___closed__3;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__15;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__3;
lean_object* l_Std_RBNode_find___main___at_Lean_LocalContext_sanitizeNames___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2;
lean_object* l_Lean_Meta_recOnSuffix___closed__1;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_casesOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("casesOn");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_casesOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_casesOnSuffix___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_recOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recOn");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_recOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_recOnSuffix___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_brecOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("brecOn");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_brecOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_brecOnSuffix___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Meta_binductionOnSuffix___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binductionOn");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_binductionOnSuffix() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_binductionOnSuffix___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_casesOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkRecOnFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_recOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_brecOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkBInductionOnFor(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_binductionOnSuffix;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<motive-univ>");
return x_1;
}
}
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Nat_repr(x_3);
return x_4;
}
}
}
lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 5);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numParams(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___main___rarg(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numIndices(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numParams(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_motivePos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 4);
x_3 = l_Lean_Meta_RecursorInfo_numIndices(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Meta_RecursorInfo_numParams(x_1);
x_4 = lean_nat_dec_le(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_1);
x_6 = lean_nat_dec_le(x_5, x_2);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_nat_dec_le(x_2, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_RecursorInfo_isMinor(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = l_Lean_Meta_RecursorInfo_numParams(x_1);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_nat_add(x_7, x_5);
x_9 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_1);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numMinors(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(x_1, x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Nat_repr(x_9);
x_11 = l_List_reprAux___main___rarg___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = lean_string_append(x_12, x_6);
lean_dec(x_6);
return x_13;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; 
x_14 = l_String_splitAux___main___closed__1;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(x_17, x_16);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Nat_repr(x_21);
x_23 = lean_string_append(x_22, x_18);
lean_dec(x_18);
return x_23;
}
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Option_HasRepr___rarg___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(x_1, x_5);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_Nat_repr(x_9);
x_11 = l_addParenHeuristic(x_10);
lean_dec(x_10);
x_12 = l_Option_HasRepr___rarg___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Option_HasRepr___rarg___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_List_reprAux___main___rarg___closed__1;
x_17 = lean_string_append(x_16, x_15);
lean_dec(x_15);
x_18 = lean_string_append(x_17, x_6);
lean_dec(x_6);
return x_18;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_19; 
x_19 = l_String_splitAux___main___closed__1;
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = 0;
x_23 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(x_22, x_21);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Option_HasRepr___rarg___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = l_Nat_repr(x_26);
x_28 = l_addParenHeuristic(x_27);
lean_dec(x_27);
x_29 = l_Option_HasRepr___rarg___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Option_HasRepr___rarg___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_string_append(x_32, x_23);
lean_dec(x_23);
return x_33;
}
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Nat_repr(x_4);
x_7 = l_List_reprAux___main___rarg___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(x_1, x_5);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
x_11 = l_String_splitAux___main___closed__1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Nat_repr(x_12);
x_15 = 0;
x_16 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(x_15, x_13);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
return x_17;
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Bool_HasRepr___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_reprAux___main___rarg___closed__1;
x_2 = l_Bool_HasRepr___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(x_1, x_5);
x_7 = lean_unbox(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1;
x_9 = lean_string_append(x_8, x_6);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
x_11 = lean_string_append(x_10, x_6);
lean_dec(x_6);
return x_11;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = 0;
x_16 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(x_15, x_14);
x_17 = lean_unbox(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Bool_HasRepr___closed__1;
x_19 = lean_string_append(x_18, x_16);
lean_dec(x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Bool_HasRepr___closed__2;
x_21 = lean_string_append(x_20, x_16);
lean_dec(x_16);
return x_21;
}
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{\n");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  name           := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_RecursorInfo_HasToString___closed__1;
x_2 = l_Lean_Meta_RecursorInfo_HasToString___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  type           := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  univs          := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  depElim        := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  recursive      := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  numArgs        := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  numParams      := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  numIndices     := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  numMinors      := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  major          := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  motive         := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  paramsAtMajor  := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  indicesAtMajor := ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_RecursorInfo_HasToString___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  produceMotive  := ");
return x_1;
}
}
lean_object* l_Lean_Meta_RecursorInfo_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Lean_Meta_RecursorInfo_HasToString___closed__3;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_Lean_Format_be___main___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = l_Lean_Meta_RecursorInfo_HasToString___closed__4;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Lean_Name_toStringWithSep___main(x_3, x_11);
x_13 = lean_string_append(x_10, x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_13, x_7);
x_15 = l_Lean_Meta_RecursorInfo_HasToString___closed__5;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__1(x_17);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
x_20 = lean_string_append(x_19, x_7);
x_21 = l_Lean_Meta_RecursorInfo_HasToString___closed__6;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
x_26 = l_Nat_repr(x_25);
x_27 = l_Lean_Meta_RecursorInfo_numParams(x_1);
x_28 = l_Nat_repr(x_27);
x_29 = l_Lean_Meta_RecursorInfo_numIndices(x_1);
x_30 = l_Nat_repr(x_29);
x_31 = l_Lean_Meta_RecursorInfo_numMinors(x_1);
x_32 = l_Nat_repr(x_31);
x_33 = lean_ctor_get(x_1, 4);
lean_inc(x_33);
x_34 = l_Nat_repr(x_33);
x_35 = lean_ctor_get(x_1, 5);
lean_inc(x_35);
x_36 = l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__3(x_35);
x_37 = lean_ctor_get(x_1, 6);
lean_inc(x_37);
x_38 = l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__5(x_37);
x_39 = lean_ctor_get(x_1, 7);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(x_39);
lean_dec(x_39);
if (x_23 == 0)
{
lean_object* x_91; 
x_91 = l_Bool_HasRepr___closed__1;
x_41 = x_91;
goto block_90;
}
else
{
lean_object* x_92; 
x_92 = l_Bool_HasRepr___closed__2;
x_41 = x_92;
goto block_90;
}
block_90:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_string_append(x_22, x_41);
lean_dec(x_41);
x_43 = lean_string_append(x_42, x_7);
x_44 = l_Lean_Meta_RecursorInfo_HasToString___closed__7;
x_45 = lean_string_append(x_43, x_44);
if (x_24 == 0)
{
lean_object* x_88; 
x_88 = l_Bool_HasRepr___closed__1;
x_46 = x_88;
goto block_87;
}
else
{
lean_object* x_89; 
x_89 = l_Bool_HasRepr___closed__2;
x_46 = x_89;
goto block_87;
}
block_87:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = lean_string_append(x_47, x_7);
x_49 = l_Lean_Meta_RecursorInfo_HasToString___closed__8;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_string_append(x_50, x_26);
lean_dec(x_26);
x_52 = lean_string_append(x_51, x_7);
x_53 = l_Lean_Meta_RecursorInfo_HasToString___closed__9;
x_54 = lean_string_append(x_52, x_53);
x_55 = lean_string_append(x_54, x_28);
x_56 = lean_string_append(x_55, x_7);
x_57 = l_Lean_Meta_RecursorInfo_HasToString___closed__10;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_string_append(x_58, x_30);
lean_dec(x_30);
x_60 = lean_string_append(x_59, x_7);
x_61 = l_Lean_Meta_RecursorInfo_HasToString___closed__11;
x_62 = lean_string_append(x_60, x_61);
x_63 = lean_string_append(x_62, x_32);
lean_dec(x_32);
x_64 = lean_string_append(x_63, x_7);
x_65 = l_Lean_Meta_RecursorInfo_HasToString___closed__12;
x_66 = lean_string_append(x_64, x_65);
x_67 = lean_string_append(x_66, x_34);
lean_dec(x_34);
x_68 = lean_string_append(x_67, x_7);
x_69 = l_Lean_Meta_RecursorInfo_HasToString___closed__13;
x_70 = lean_string_append(x_68, x_69);
x_71 = lean_string_append(x_70, x_28);
lean_dec(x_28);
x_72 = lean_string_append(x_71, x_7);
x_73 = l_Lean_Meta_RecursorInfo_HasToString___closed__14;
x_74 = lean_string_append(x_72, x_73);
x_75 = lean_string_append(x_74, x_36);
lean_dec(x_36);
x_76 = lean_string_append(x_75, x_7);
x_77 = l_Lean_Meta_RecursorInfo_HasToString___closed__15;
x_78 = lean_string_append(x_76, x_77);
x_79 = lean_string_append(x_78, x_38);
lean_dec(x_38);
x_80 = lean_string_append(x_79, x_7);
x_81 = l_Lean_Meta_RecursorInfo_HasToString___closed__16;
x_82 = lean_string_append(x_80, x_81);
x_83 = lean_string_append(x_82, x_40);
lean_dec(x_40);
x_84 = lean_string_append(x_83, x_7);
x_85 = l_Std_PersistentArray_Stats_toString___closed__4;
x_86 = lean_string_append(x_84, x_85);
return x_86;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(x_3, x_2);
return x_4;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(x_3, x_2);
return x_4;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(x_3, x_2);
return x_4;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_9);
x_20 = lean_box(0);
x_11 = x_20;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_getConstInfoInduct___rarg___lambda__1___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_10);
return x_17;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
if (lean_obj_tag(x_21) == 5)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_21);
x_33 = lean_box(0);
x_23 = x_33;
goto block_30;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_getConstInfoInduct___rarg___lambda__1___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_22);
return x_29;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(lean_object* x_1, lean_object* x_2) {
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
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_nat_add(x_1, x_5);
lean_dec(x_5);
x_8 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_nat_add(x_1, x_9);
lean_dec(x_9);
x_12 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_RecursorVal_getInduct(x_2);
lean_inc(x_8);
x_9 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_List_lengthAux___main___rarg(x_13, x_14);
lean_dec(x_13);
lean_inc(x_15);
x_16 = l_List_range(x_15);
x_17 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_16);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_List_lengthAux___main___rarg(x_19, x_14);
lean_dec(x_19);
x_21 = lean_nat_dec_eq(x_20, x_15);
lean_dec(x_15);
lean_dec(x_20);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_inc(x_22);
x_25 = l_List_replicate___rarg(x_22, x_24);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_inc(x_26);
x_27 = l_List_range(x_26);
x_28 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_27);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_29);
x_30 = l_List_range(x_29);
x_31 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(x_26, x_30);
x_32 = lean_nat_add(x_29, x_26);
lean_dec(x_26);
lean_dec(x_29);
x_33 = lean_nat_add(x_32, x_22);
lean_dec(x_22);
lean_dec(x_32);
x_34 = lean_ctor_get(x_2, 4);
lean_inc(x_34);
x_35 = lean_nat_add(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_35);
x_38 = lean_ctor_get_uint8(x_11, sizeof(void*)*5);
lean_dec(x_11);
x_39 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_21 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_17);
x_42 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_41);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_42, 5, x_28);
lean_ctor_set(x_42, 6, x_31);
lean_ctor_set(x_42, 7, x_25);
lean_ctor_set_uint8(x_42, sizeof(void*)*8, x_23);
lean_ctor_set_uint8(x_42, sizeof(void*)*8 + 1, x_38);
lean_ctor_set(x_9, 0, x_42);
return x_9;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_8);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_37);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_28);
lean_ctor_set(x_43, 6, x_31);
lean_ctor_set(x_43, 7, x_25);
lean_ctor_set_uint8(x_43, sizeof(void*)*8, x_23);
lean_ctor_set_uint8(x_43, sizeof(void*)*8 + 1, x_38);
lean_ctor_set(x_9, 0, x_43);
return x_9;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_9, 0);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_9);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_List_lengthAux___main___rarg(x_47, x_48);
lean_dec(x_47);
lean_inc(x_49);
x_50 = l_List_range(x_49);
x_51 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_50);
x_52 = lean_ctor_get(x_2, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_List_lengthAux___main___rarg(x_53, x_48);
lean_dec(x_53);
x_55 = lean_nat_dec_eq(x_54, x_49);
lean_dec(x_49);
lean_dec(x_54);
x_56 = lean_ctor_get(x_2, 5);
lean_inc(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_inc(x_56);
x_59 = l_List_replicate___rarg(x_56, x_58);
x_60 = lean_ctor_get(x_2, 2);
lean_inc(x_60);
lean_inc(x_60);
x_61 = l_List_range(x_60);
x_62 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_61);
x_63 = lean_ctor_get(x_2, 3);
lean_inc(x_63);
lean_inc(x_63);
x_64 = l_List_range(x_63);
x_65 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(x_60, x_64);
x_66 = lean_nat_add(x_63, x_60);
lean_dec(x_60);
lean_dec(x_63);
x_67 = lean_nat_add(x_66, x_56);
lean_dec(x_56);
lean_dec(x_66);
x_68 = lean_ctor_get(x_2, 4);
lean_inc(x_68);
x_69 = lean_nat_add(x_67, x_68);
lean_dec(x_68);
lean_dec(x_67);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_69, x_70);
lean_dec(x_69);
x_72 = lean_ctor_get_uint8(x_44, sizeof(void*)*5);
lean_dec(x_44);
x_73 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_55 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_51);
x_76 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_8);
lean_ctor_set(x_76, 2, x_75);
lean_ctor_set(x_76, 3, x_71);
lean_ctor_set(x_76, 4, x_73);
lean_ctor_set(x_76, 5, x_62);
lean_ctor_set(x_76, 6, x_65);
lean_ctor_set(x_76, 7, x_59);
lean_ctor_set_uint8(x_76, sizeof(void*)*8, x_57);
lean_ctor_set_uint8(x_76, sizeof(void*)*8 + 1, x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_45);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_8);
lean_ctor_set(x_78, 2, x_51);
lean_ctor_set(x_78, 3, x_71);
lean_ctor_set(x_78, 4, x_73);
lean_ctor_set(x_78, 5, x_62);
lean_ctor_set(x_78, 6, x_65);
lean_ctor_set(x_78, 7, x_59);
lean_ctor_set_uint8(x_78, sizeof(void*)*8, x_57);
lean_ctor_set_uint8(x_78, sizeof(void*)*8 + 1, x_72);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_45);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_9);
if (x_80 == 0)
{
return x_9;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_9, 0);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_9);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; 
lean_free_object(x_7);
lean_dec(x_9);
x_20 = lean_box(0);
x_11 = x_20;
goto block_18;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_getConstInfoRec___rarg___lambda__1___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_16, x_2, x_3, x_4, x_5, x_10);
return x_17;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
if (lean_obj_tag(x_21) == 7)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_21, 0);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_22);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_21);
x_33 = lean_box(0);
x_23 = x_33;
goto block_30;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_23);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_1);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_getConstInfoRec___rarg___lambda__1___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_2, x_3, x_4, x_5, x_22);
return x_29;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_auxRecExt;
x_14 = l_Lean_TagDeclarationExtension_isTagged(x_13, x_12, x_1);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_55; uint8_t x_56; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_55 = l_Lean_Meta_recOnSuffix;
x_56 = lean_string_dec_eq(x_17, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Meta_casesOnSuffix;
x_58 = lean_string_dec_eq(x_17, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Meta_brecOnSuffix;
x_60 = lean_string_dec_eq(x_17, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_17);
lean_dec(x_16);
x_61 = lean_box(0);
lean_ctor_set(x_8, 0, x_61);
return x_8;
}
else
{
lean_object* x_62; 
lean_free_object(x_8);
x_62 = lean_box(0);
x_18 = x_62;
goto block_54;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_8);
x_63 = lean_box(0);
x_18 = x_63;
goto block_54;
}
}
else
{
lean_object* x_64; 
lean_free_object(x_8);
x_64 = lean_box(0);
x_18 = x_64;
goto block_54;
}
block_54:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
x_19 = l_Lean_mkRecFor___closed__1;
x_20 = lean_name_mk_string(x_16, x_19);
x_21 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1(x_20, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 3);
lean_inc(x_25);
x_26 = lean_nat_add(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
x_27 = l_Lean_Meta_casesOnSuffix;
x_28 = lean_string_dec_eq(x_17, x_27);
lean_dec(x_17);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_nat_add(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_23);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_26, x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 3);
lean_inc(x_38);
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
x_40 = l_Lean_Meta_casesOnSuffix;
x_41 = lean_string_dec_eq(x_17, x_40);
lean_dec(x_17);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_35, 4);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_nat_add(x_39, x_42);
lean_dec(x_42);
lean_dec(x_39);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_39, x_46);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_17);
x_50 = !lean_is_exclusive(x_21);
if (x_50 == 0)
{
return x_21;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_21, 0);
x_52 = lean_ctor_get(x_21, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_21);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_1);
x_65 = lean_box(0);
lean_ctor_set(x_8, 0, x_65);
return x_8;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_8, 0);
x_67 = lean_ctor_get(x_8, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_8);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_auxRecExt;
x_70 = l_Lean_TagDeclarationExtension_isTagged(x_69, x_68, x_1);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_100; uint8_t x_101; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_100 = l_Lean_Meta_recOnSuffix;
x_101 = lean_string_dec_eq(x_74, x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Meta_casesOnSuffix;
x_103 = lean_string_dec_eq(x_74, x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = l_Lean_Meta_brecOnSuffix;
x_105 = lean_string_dec_eq(x_74, x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_74);
lean_dec(x_73);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_67);
return x_107;
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_75 = x_108;
goto block_99;
}
}
else
{
lean_object* x_109; 
x_109 = lean_box(0);
x_75 = x_109;
goto block_99;
}
}
else
{
lean_object* x_110; 
x_110 = lean_box(0);
x_75 = x_110;
goto block_99;
}
block_99:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_75);
x_76 = l_Lean_mkRecFor___closed__1;
x_77 = lean_name_mk_string(x_73, x_76);
x_78 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1(x_77, x_3, x_4, x_5, x_6, x_67);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 2);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 3);
lean_inc(x_83);
x_84 = lean_nat_add(x_82, x_83);
lean_dec(x_83);
lean_dec(x_82);
x_85 = l_Lean_Meta_casesOnSuffix;
x_86 = lean_string_dec_eq(x_74, x_85);
lean_dec(x_74);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_79, 4);
lean_inc(x_87);
lean_dec(x_79);
x_88 = lean_nat_add(x_84, x_87);
lean_dec(x_87);
lean_dec(x_84);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
if (lean_is_scalar(x_81)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_81;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_80);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_79);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_84, x_91);
lean_dec(x_84);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_80);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_74);
x_95 = lean_ctor_get(x_78, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_78, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_97 = x_78;
} else {
 lean_dec_ref(x_78);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_67);
return x_112;
}
}
}
}
else
{
lean_object* x_113; 
lean_dec(x_1);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_2);
lean_ctor_set(x_113, 1, x_7);
return x_113;
}
}
}
lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_4);
x_8 = l_Lean_Expr_isFVar(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_4);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_4, x_10);
lean_dec(x_4);
x_4 = x_11;
goto _start;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid user defined recursor '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', result type must be of the form (C t), ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("where C is a bound variable, and t is a (possibly empty) sequence of bound variables");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_22; 
x_22 = l_Lean_Expr_isFVar(x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_box(0);
x_9 = x_23;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_3);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_3, x_3, x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_box(0);
x_9 = x_29;
goto block_21;
}
}
block_21:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_10 = l_System_FilePath_dirName___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_1);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_19, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
return x_3;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = lean_expr_eqv(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
return x_3;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_RecursorInfo_4__getNumParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_expr_eqv(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_2, x_1, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid user defined recursor, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("and position of the major premise was not specified ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid major premise position for user defined recursor, recursor has only ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Array_back___at___private_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_12, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_22, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_30 = l_System_FilePath_dirName___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_1);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_41, x_6, x_7, x_8, x_9, x_10);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_2, 0);
x_48 = lean_array_get_size(x_3);
x_49 = lean_nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = l_Nat_repr(x_48);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_56, x_6, x_7, x_8, x_9, x_10);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_48);
x_58 = lean_array_fget(x_3, x_47);
x_59 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_5, x_58);
x_60 = lean_box(x_59);
lean_inc(x_47);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_47);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_10);
return x_63;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_8 = x_17;
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
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor parameter");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_Inhabited;
x_12 = lean_array_get(x_11, x_1, x_2);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_12);
x_14 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_12, x_3, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
lean_inc(x_6);
x_18 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_17, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = l_Lean_LocalDecl_binderInfo(x_20);
lean_dec(x_20);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_18);
lean_dec(x_5);
x_24 = l_System_FilePath_dirName___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_4);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_31, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = lean_array_push(x_5, x_15);
lean_ctor_set(x_18, 0, x_33);
return x_18;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = l_Lean_LocalDecl_binderInfo(x_34);
lean_dec(x_34);
x_37 = l_Lean_BinderInfo_isInstImplicit(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
x_38 = l_System_FilePath_dirName___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_4);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_45, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_47 = lean_array_push(x_5, x_15);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_14, 0);
lean_dec(x_54);
x_55 = lean_array_push(x_5, x_15);
lean_ctor_set(x_14, 0, x_55);
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_dec(x_14);
x_57 = lean_array_push(x_5, x_15);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_14);
if (x_59 == 0)
{
return x_14;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_14, 0);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_14);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_6, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_nat_sub(x_5, x_16);
x_19 = lean_nat_sub(x_18, x_15);
lean_dec(x_18);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___boxed), 10, 5);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_1);
lean_closure_set(x_20, 4, x_7);
x_21 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed), 12, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
lean_closure_set(x_21, 4, x_5);
lean_closure_set(x_21, 5, x_16);
x_22 = lean_apply_9(x_17, lean_box(0), lean_box(0), x_20, x_21, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_ctor_get(x_4, 0);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_7(x_24, lean_box(0), x_7, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_11 = l_Array_empty___closed__1;
lean_inc(x_3);
x_12 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_4, x_10, x_3, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
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
x_18 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
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
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_3, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget(x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Meta_isExprDefEq___at_Lean_Meta_isExprDefEqGuarded___spec__1(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_8 = x_17;
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
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor index");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_nat_sub(x_1, x_2);
x_14 = lean_nat_add(x_13, x_3);
lean_dec(x_13);
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_array_get(x_15, x_4, x_14);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_16, x_5, x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_System_FilePath_dirName___closed__1;
x_22 = l_Lean_Name_toStringWithSep___main(x_21, x_6);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_19, 0);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_array_push(x_7, x_32);
lean_ctor_set(x_18, 0, x_33);
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_array_push(x_7, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_18);
if (x_38 == 0)
{
return x_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_18, 0);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
x_20 = lean_nat_sub(x_7, x_18);
x_21 = lean_nat_sub(x_20, x_17);
lean_dec(x_20);
lean_inc(x_1);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_3);
x_22 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___boxed), 12, 7);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_2);
lean_closure_set(x_22, 4, x_5);
lean_closure_set(x_22, 5, x_1);
lean_closure_set(x_22, 6, x_9);
x_23 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed), 14, 8);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_18);
x_24 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_22, x_23, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_7(x_26, lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_12 = l_Array_empty___closed__1;
lean_inc_n(x_4, 2);
x_13 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_4, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
return x_15;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , motive result sort must be Prop or (Sort u) where u is a universe level parameter");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; 
lean_dec(x_1);
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
case 4:
{
lean_object* x_21; 
lean_dec(x_1);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_7);
return x_21;
}
default: 
{
lean_object* x_22; 
x_22 = lean_box(0);
x_8 = x_22;
goto block_18;
}
}
}
else
{
lean_object* x_23; 
x_23 = lean_box(0);
x_8 = x_23;
goto block_18;
}
block_18:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_9 = l_System_FilePath_dirName___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_16, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_level_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
}
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , major premise type does not contain universe level parameter '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_mkLevelParam(x_1);
x_12 = lean_level_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_11, x_3, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_4);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_28, x_6, x_7, x_8, x_9, x_10);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_push(x_5, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_array_push(x_5, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_10);
return x_36;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_2, x_3, x_4, x_6, x_5, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_7(x_13, lean_box(0), x_5, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___boxed), 10, 5);
lean_closure_set(x_18, 0, x_15);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_1);
lean_closure_set(x_18, 4, x_5);
x_19 = lean_alloc_closure((void*)(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__2), 11, 5);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_16);
x_20 = lean_apply_9(x_17, lean_box(0), lean_box(0), x_18, x_19, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_List_redLength___main___rarg(x_4);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___main___rarg(x_4, x_11);
x_13 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_14 = l_Array_empty___closed__1;
x_15 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_3, x_12, x_13, x_14, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
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
x_21 = l_Array_toList___rarg(x_19);
lean_dec(x_19);
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
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; size_t x_97; size_t x_98; lean_object* x_99; size_t x_100; uint8_t x_101; 
x_97 = lean_ptr_addr(x_3);
x_98 = x_2 == 0 ? 0 : x_97 % x_2;
x_99 = lean_array_uget(x_4, x_98);
x_100 = lean_ptr_addr(x_99);
lean_dec(x_99);
x_101 = x_100 == x_97;
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
lean_inc(x_3);
x_102 = lean_array_uset(x_4, x_98, x_3);
x_103 = 0;
x_5 = x_103;
x_6 = x_102;
goto block_96;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_5 = x_104;
x_6 = x_4;
goto block_96;
}
block_96:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = lean_expr_eqv(x_3, x_1);
if (x_7 == 0)
{
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_8, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_3 = x_9;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_10, 0, x_18);
return x_10;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_21 = x_11;
} else {
 lean_dec_ref(x_11);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
}
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
lean_dec(x_3);
x_26 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_24, x_6);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_3 = x_25;
x_4 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = lean_ctor_get(x_27, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_37 = x_27;
} else {
 lean_dec_ref(x_27);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
case 7:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
lean_dec(x_3);
x_42 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_40, x_6);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_3 = x_41;
x_4 = x_44;
goto _start;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_42, 0);
lean_dec(x_47);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_42, 0, x_50);
return x_42;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_dec(x_42);
x_52 = lean_ctor_get(x_43, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
case 8:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_3, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 3);
lean_inc(x_58);
lean_dec(x_3);
x_59 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_56, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_57, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_3 = x_58;
x_4 = x_64;
goto _start;
}
else
{
uint8_t x_66; 
lean_dec(x_58);
x_66 = !lean_is_exclusive(x_62);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_62, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_62;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_62, 0, x_70);
return x_62;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_62, 1);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_ctor_get(x_63, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_73 = x_63;
} else {
 lean_dec_ref(x_63);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_58);
lean_dec(x_57);
x_76 = !lean_is_exclusive(x_59);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_59, 0);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_60, 0);
lean_inc(x_79);
lean_dec(x_60);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_59, 0, x_80);
return x_59;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_59, 1);
lean_inc(x_81);
lean_dec(x_59);
x_82 = lean_ctor_get(x_60, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_83 = x_60;
} else {
 lean_dec_ref(x_60);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
}
case 10:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
lean_dec(x_3);
x_3 = x_86;
x_4 = x_6;
goto _start;
}
case 11:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_3, 2);
lean_inc(x_88);
lean_dec(x_3);
x_3 = x_88;
x_4 = x_6;
goto _start;
}
default: 
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_3);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_6);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_3);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_6);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_3);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_6);
return x_95;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_nat_dec_lt(x_5, x_4);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_3, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = 8192;
x_21 = l_Lean_Expr_FindImpl_initCache;
x_22 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_20, x_18, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
x_10 = x_19;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = 1;
x_28 = lean_box(x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
x_31 = 8192;
x_32 = l_Lean_Expr_FindImpl_initCache;
x_33 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_31, x_29, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_5, x_35);
lean_dec(x_5);
x_5 = x_36;
x_10 = x_30;
goto _start;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_30);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_41 = !lean_is_exclusive(x_16);
if (x_41 == 0)
{
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 0);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_16);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
x_19 = lean_expr_eqv(x_5, x_1);
lean_dec(x_5);
x_20 = lean_box(x_19);
x_21 = lean_array_push(x_2, x_20);
if (x_3 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_array_get_size(x_4);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_4, x_4, x_22, x_23, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_21);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_36 = lean_box(x_3);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_12);
return x_38;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_11);
x_13 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_5, x_28);
x_30 = lean_nat_dec_lt(x_3, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_nat_sub(x_6, x_7);
x_32 = lean_nat_dec_le(x_31, x_3);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_13 = x_33;
goto block_27;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_3, x_6);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_13 = x_35;
goto block_27;
}
else
{
lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_array_get(x_16, x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_17, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed), 10, 3);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_14);
lean_closure_set(x_21, 2, x_15);
x_22 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_8, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_8, x_17);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
x_20 = lean_nat_sub(x_7, x_18);
x_21 = lean_nat_sub(x_20, x_17);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_5);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2___boxed), 12, 7);
lean_closure_set(x_22, 0, x_9);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_21);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_2);
lean_closure_set(x_22, 5, x_4);
lean_closure_set(x_22, 6, x_3);
x_23 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed), 14, 8);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_7);
lean_closure_set(x_23, 7, x_18);
x_24 = lean_apply_9(x_19, lean_box(0), lean_box(0), x_22, x_23, x_10, x_11, x_12, x_13, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_6, 0);
lean_inc(x_25);
lean_dec(x_6);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_apply_7(x_26, lean_box(0), x_9, x_10, x_11, x_12, x_13, x_14);
return x_27;
}
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_empty___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_1);
x_12 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_13 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_11);
x_14 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_12, x_11, x_11, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Array_toList___rarg(x_20);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = l_Array_toList___rarg(x_26);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
return x_14;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
x_34 = lean_ctor_get(x_14, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_14);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
return x_15;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', motive must have a type of the form ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(i : B A) is a (possibly empty) telescope (aka indices), and I is a constant");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_25; 
x_25 = l_Lean_Expr_isSort(x_3);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_10 = x_26;
goto block_24;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_array_get_size(x_2);
x_28 = lean_array_get_size(x_4);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_10 = x_30;
goto block_24;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_9);
return x_32;
}
}
block_24:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_11 = l_System_FilePath_dirName___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_1);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_22, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_15, x_14, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_15, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ConstantInfo_lparams(x_3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_1);
x_27 = l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_26, x_24, x_4, x_16, x_17, x_18, x_19, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_5);
x_30 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_5, x_6, x_7, x_8, x_9, x_16, x_17, x_18, x_19, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_5);
lean_dec(x_5);
x_36 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_10);
lean_ctor_set(x_36, 2, x_28);
lean_ctor_set(x_36, 3, x_35);
lean_ctor_set(x_36, 4, x_8);
lean_ctor_set(x_36, 5, x_12);
lean_ctor_set(x_36, 6, x_13);
lean_ctor_set(x_36, 7, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*8, x_11);
x_37 = lean_unbox(x_34);
lean_dec(x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*8 + 1, x_37);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_array_get_size(x_5);
lean_dec(x_5);
x_43 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_28);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_8);
lean_ctor_set(x_43, 5, x_12);
lean_ctor_set(x_43, 6, x_13);
lean_ctor_set(x_43, 7, x_40);
lean_ctor_set_uint8(x_43, sizeof(void*)*8, x_11);
x_44 = lean_unbox(x_41);
lean_dec(x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*8 + 1, x_44);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_39);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_28);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
return x_27;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_27, 0);
x_52 = lean_ctor_get(x_27, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_27);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_23);
if (x_54 == 0)
{
return x_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_23, 0);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_21);
if (x_58 == 0)
{
return x_21;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_21, 0);
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_21);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', type of the major premise must be of the form (I ...), where I is a constant");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_11)) {
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_4, x_7, x_12, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
x_24 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_4, x_8, x_10, x_12, x_14, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_5);
x_27 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_5, x_14, x_15, x_16, x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(x_9);
x_31 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 20, 13);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_6);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_20);
lean_closure_set(x_31, 4, x_4);
lean_closure_set(x_31, 5, x_7);
lean_closure_set(x_31, 6, x_10);
lean_closure_set(x_31, 7, x_8);
lean_closure_set(x_31, 8, x_5);
lean_closure_set(x_31, 9, x_19);
lean_closure_set(x_31, 10, x_30);
lean_closure_set(x_31, 11, x_22);
lean_closure_set(x_31, 12, x_25);
x_32 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_28, x_31, x_14, x_15, x_16, x_17, x_29);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_array_set(x_12, x_13, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_13, x_48);
lean_dec(x_13);
x_11 = x_45;
x_12 = x_47;
x_13 = x_49;
goto _start;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = l_System_FilePath_dirName___closed__1;
x_52 = l_Lean_Name_toStringWithSep___main(x_51, x_2);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
x_58 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_58, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_59;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
switch (lean_obj_tag(x_11)) {
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_10);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_3, x_6, x_12, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_12, x_14, x_15, x_16, x_17, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_4);
x_27 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_4, x_14, x_15, x_16, x_17, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(x_8);
x_31 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 20, 13);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_5);
lean_closure_set(x_31, 2, x_1);
lean_closure_set(x_31, 3, x_20);
lean_closure_set(x_31, 4, x_3);
lean_closure_set(x_31, 5, x_6);
lean_closure_set(x_31, 6, x_9);
lean_closure_set(x_31, 7, x_7);
lean_closure_set(x_31, 8, x_4);
lean_closure_set(x_31, 9, x_19);
lean_closure_set(x_31, 10, x_30);
lean_closure_set(x_31, 11, x_22);
lean_closure_set(x_31, 12, x_25);
x_32 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_28, x_31, x_14, x_15, x_16, x_17, x_29);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
return x_21;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_21, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_21);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_array_set(x_12, x_13, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_13, x_48);
lean_dec(x_13);
x_11 = x_45;
x_12 = x_47;
x_13 = x_49;
goto _start;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_52, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_53;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', indices must occur before major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_14; 
lean_dec(x_8);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_16);
lean_inc(x_2);
x_18 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_55; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_55 = lean_unbox(x_24);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_array_get_size(x_7);
x_25 = x_56;
goto block_54;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_get_size(x_7);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_sub(x_57, x_58);
lean_dec(x_57);
x_25 = x_59;
goto block_54;
}
block_54:
{
uint8_t x_26; 
x_26 = lean_nat_dec_lt(x_23, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_22, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppNumArgsAux___main(x_28, x_16);
x_31 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_30);
x_32 = lean_mk_array(x_30, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_sub(x_30, x_33);
lean_dec(x_30);
x_35 = lean_unbox(x_24);
lean_dec(x_24);
x_36 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_17, x_23, x_35, x_25, x_28, x_32, x_34, x_9, x_10, x_11, x_12, x_29);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_41 = l_System_FilePath_dirName___closed__1;
x_42 = l_Lean_Name_toStringWithSep___main(x_41, x_2);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_48, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_14);
if (x_64 == 0)
{
return x_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_14, 0);
x_66 = lean_ctor_get(x_14, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_14);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
case 1:
{
lean_object* x_68; 
lean_dec(x_8);
lean_inc(x_2);
x_68 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_70);
lean_inc(x_2);
x_72 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_109; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_109 = lean_unbox(x_78);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_array_get_size(x_7);
x_79 = x_110;
goto block_108;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_array_get_size(x_7);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_sub(x_111, x_112);
lean_dec(x_111);
x_79 = x_113;
goto block_108;
}
block_108:
{
uint8_t x_80; 
x_80 = lean_nat_dec_lt(x_77, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_81 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_76, x_9, x_10, x_11, x_12, x_75);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Expr_getAppNumArgsAux___main(x_82, x_70);
x_85 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_84);
x_86 = lean_mk_array(x_84, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_84, x_87);
lean_dec(x_84);
x_89 = lean_unbox(x_78);
lean_dec(x_78);
x_90 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_71, x_77, x_89, x_79, x_82, x_86, x_88, x_9, x_10, x_11, x_12, x_83);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_71);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_81);
if (x_91 == 0)
{
return x_81;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_81, 0);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_81);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = l_System_FilePath_dirName___closed__1;
x_96 = l_Lean_Name_toStringWithSep___main(x_95, x_2);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_102, x_9, x_10, x_11, x_12, x_75);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_71);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_72);
if (x_114 == 0)
{
return x_72;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_72, 0);
x_116 = lean_ctor_get(x_72, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_72);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_68);
if (x_118 == 0)
{
return x_68;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_68, 0);
x_120 = lean_ctor_get(x_68, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_68);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
case 2:
{
lean_object* x_122; 
lean_dec(x_8);
lean_inc(x_2);
x_122 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_124);
lean_inc(x_2);
x_126 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_123);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_163; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_163 = lean_unbox(x_132);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_array_get_size(x_7);
x_133 = x_164;
goto block_162;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_array_get_size(x_7);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_nat_sub(x_165, x_166);
lean_dec(x_165);
x_133 = x_167;
goto block_162;
}
block_162:
{
uint8_t x_134; 
x_134 = lean_nat_dec_lt(x_131, x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_135 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_130, x_9, x_10, x_11, x_12, x_129);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Expr_getAppNumArgsAux___main(x_136, x_124);
x_139 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_138);
x_140 = lean_mk_array(x_138, x_139);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_sub(x_138, x_141);
lean_dec(x_138);
x_143 = lean_unbox(x_132);
lean_dec(x_132);
x_144 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_125, x_131, x_143, x_133, x_136, x_140, x_142, x_9, x_10, x_11, x_12, x_137);
return x_144;
}
else
{
uint8_t x_145; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_125);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_135);
if (x_145 == 0)
{
return x_135;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_135, 0);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_135);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_125);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_149 = l_System_FilePath_dirName___closed__1;
x_150 = l_Lean_Name_toStringWithSep___main(x_149, x_2);
x_151 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_154 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_156 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_156, x_9, x_10, x_11, x_12, x_129);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
return x_157;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_157);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_125);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_126);
if (x_168 == 0)
{
return x_126;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_126, 0);
x_170 = lean_ctor_get(x_126, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_126);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_122);
if (x_172 == 0)
{
return x_122;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_122, 0);
x_174 = lean_ctor_get(x_122, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_122);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
case 3:
{
lean_object* x_176; 
lean_dec(x_8);
lean_inc(x_2);
x_176 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_178);
lean_inc(x_2);
x_180 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_177);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_217; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
lean_dec(x_181);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
lean_dec(x_182);
x_217 = lean_unbox(x_186);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_array_get_size(x_7);
x_187 = x_218;
goto block_216;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_array_get_size(x_7);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_sub(x_219, x_220);
lean_dec(x_219);
x_187 = x_221;
goto block_216;
}
block_216:
{
uint8_t x_188; 
x_188 = lean_nat_dec_lt(x_185, x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_189 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_184, x_9, x_10, x_11, x_12, x_183);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_Expr_getAppNumArgsAux___main(x_190, x_178);
x_193 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_192);
x_194 = lean_mk_array(x_192, x_193);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_nat_sub(x_192, x_195);
lean_dec(x_192);
x_197 = lean_unbox(x_186);
lean_dec(x_186);
x_198 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_179, x_185, x_197, x_187, x_190, x_194, x_196, x_9, x_10, x_11, x_12, x_191);
return x_198;
}
else
{
uint8_t x_199; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_179);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_189);
if (x_199 == 0)
{
return x_189;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_189, 0);
x_201 = lean_ctor_get(x_189, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_189);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_179);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_203 = l_System_FilePath_dirName___closed__1;
x_204 = l_Lean_Name_toStringWithSep___main(x_203, x_2);
x_205 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_208 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
x_209 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_210, x_9, x_10, x_11, x_12, x_183);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
return x_211;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_211);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_179);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_180);
if (x_222 == 0)
{
return x_180;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_180, 0);
x_224 = lean_ctor_get(x_180, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_180);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
else
{
uint8_t x_226; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_176);
if (x_226 == 0)
{
return x_176;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_176, 0);
x_228 = lean_ctor_get(x_176, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_176);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
case 4:
{
lean_object* x_230; 
lean_dec(x_8);
lean_inc(x_2);
x_230 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_unsigned_to_nat(0u);
x_233 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_232);
lean_inc(x_2);
x_234 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_271; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_236, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_236, 1);
lean_inc(x_240);
lean_dec(x_236);
x_271 = lean_unbox(x_240);
if (x_271 == 0)
{
lean_object* x_272; 
x_272 = lean_array_get_size(x_7);
x_241 = x_272;
goto block_270;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_array_get_size(x_7);
x_274 = lean_unsigned_to_nat(1u);
x_275 = lean_nat_sub(x_273, x_274);
lean_dec(x_273);
x_241 = x_275;
goto block_270;
}
block_270:
{
uint8_t x_242; 
x_242 = lean_nat_dec_lt(x_239, x_241);
if (x_242 == 0)
{
lean_object* x_243; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_243 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_238, x_9, x_10, x_11, x_12, x_237);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lean_Expr_getAppNumArgsAux___main(x_244, x_232);
x_247 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_246);
x_248 = lean_mk_array(x_246, x_247);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_nat_sub(x_246, x_249);
lean_dec(x_246);
x_251 = lean_unbox(x_240);
lean_dec(x_240);
x_252 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_233, x_239, x_251, x_241, x_244, x_248, x_250, x_9, x_10, x_11, x_12, x_245);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_233);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_253 = !lean_is_exclusive(x_243);
if (x_253 == 0)
{
return x_243;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_243, 0);
x_255 = lean_ctor_get(x_243, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_243);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_233);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_257 = l_System_FilePath_dirName___closed__1;
x_258 = l_Lean_Name_toStringWithSep___main(x_257, x_2);
x_259 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_262 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_264 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_264, x_9, x_10, x_11, x_12, x_237);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_266 = !lean_is_exclusive(x_265);
if (x_266 == 0)
{
return x_265;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_265, 0);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_265);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_233);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_234);
if (x_276 == 0)
{
return x_234;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_234, 0);
x_278 = lean_ctor_get(x_234, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_234);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_280 = !lean_is_exclusive(x_230);
if (x_280 == 0)
{
return x_230;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_230, 0);
x_282 = lean_ctor_get(x_230, 1);
lean_inc(x_282);
lean_inc(x_281);
lean_dec(x_230);
x_283 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
return x_283;
}
}
}
case 5:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_6, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_6, 1);
lean_inc(x_285);
lean_dec(x_6);
x_286 = lean_array_set(x_7, x_8, x_285);
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_nat_sub(x_8, x_287);
lean_dec(x_8);
x_6 = x_284;
x_7 = x_286;
x_8 = x_288;
goto _start;
}
case 6:
{
lean_object* x_290; 
lean_dec(x_8);
lean_inc(x_2);
x_290 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = lean_unsigned_to_nat(0u);
x_293 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_292);
lean_inc(x_2);
x_294 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_291);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_331; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec(x_296);
x_331 = lean_unbox(x_300);
if (x_331 == 0)
{
lean_object* x_332; 
x_332 = lean_array_get_size(x_7);
x_301 = x_332;
goto block_330;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_array_get_size(x_7);
x_334 = lean_unsigned_to_nat(1u);
x_335 = lean_nat_sub(x_333, x_334);
lean_dec(x_333);
x_301 = x_335;
goto block_330;
}
block_330:
{
uint8_t x_302; 
x_302 = lean_nat_dec_lt(x_299, x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_303 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_298, x_9, x_10, x_11, x_12, x_297);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_311; lean_object* x_312; 
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_303, 1);
lean_inc(x_305);
lean_dec(x_303);
x_306 = l_Lean_Expr_getAppNumArgsAux___main(x_304, x_292);
x_307 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_306);
x_308 = lean_mk_array(x_306, x_307);
x_309 = lean_unsigned_to_nat(1u);
x_310 = lean_nat_sub(x_306, x_309);
lean_dec(x_306);
x_311 = lean_unbox(x_300);
lean_dec(x_300);
x_312 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_293, x_299, x_311, x_301, x_304, x_308, x_310, x_9, x_10, x_11, x_12, x_305);
return x_312;
}
else
{
uint8_t x_313; 
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_313 = !lean_is_exclusive(x_303);
if (x_313 == 0)
{
return x_303;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_303, 0);
x_315 = lean_ctor_get(x_303, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_303);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_317 = l_System_FilePath_dirName___closed__1;
x_318 = l_Lean_Name_toStringWithSep___main(x_317, x_2);
x_319 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_324 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_324, x_9, x_10, x_11, x_12, x_297);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
return x_325;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_325, 0);
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_325);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_293);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_336 = !lean_is_exclusive(x_294);
if (x_336 == 0)
{
return x_294;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_294, 0);
x_338 = lean_ctor_get(x_294, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_294);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_290);
if (x_340 == 0)
{
return x_290;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_290, 0);
x_342 = lean_ctor_get(x_290, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_290);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
case 7:
{
lean_object* x_344; 
lean_dec(x_8);
lean_inc(x_2);
x_344 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_344, 1);
lean_inc(x_345);
lean_dec(x_344);
x_346 = lean_unsigned_to_nat(0u);
x_347 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_346);
lean_inc(x_2);
x_348 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_345);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_385; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
lean_dec(x_349);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
lean_dec(x_350);
x_385 = lean_unbox(x_354);
if (x_385 == 0)
{
lean_object* x_386; 
x_386 = lean_array_get_size(x_7);
x_355 = x_386;
goto block_384;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_array_get_size(x_7);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_nat_sub(x_387, x_388);
lean_dec(x_387);
x_355 = x_389;
goto block_384;
}
block_384:
{
uint8_t x_356; 
x_356 = lean_nat_dec_lt(x_353, x_355);
if (x_356 == 0)
{
lean_object* x_357; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_357 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_352, x_9, x_10, x_11, x_12, x_351);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = l_Lean_Expr_getAppNumArgsAux___main(x_358, x_346);
x_361 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_360);
x_362 = lean_mk_array(x_360, x_361);
x_363 = lean_unsigned_to_nat(1u);
x_364 = lean_nat_sub(x_360, x_363);
lean_dec(x_360);
x_365 = lean_unbox(x_354);
lean_dec(x_354);
x_366 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_347, x_353, x_365, x_355, x_358, x_362, x_364, x_9, x_10, x_11, x_12, x_359);
return x_366;
}
else
{
uint8_t x_367; 
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_347);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_367 = !lean_is_exclusive(x_357);
if (x_367 == 0)
{
return x_357;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_357, 0);
x_369 = lean_ctor_get(x_357, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_357);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; 
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_347);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_371 = l_System_FilePath_dirName___closed__1;
x_372 = l_Lean_Name_toStringWithSep___main(x_371, x_2);
x_373 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_374, 0, x_373);
x_375 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_376 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
x_377 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_378, x_9, x_10, x_11, x_12, x_351);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_380 = !lean_is_exclusive(x_379);
if (x_380 == 0)
{
return x_379;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_379, 0);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_379);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
}
else
{
uint8_t x_390; 
lean_dec(x_347);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_348);
if (x_390 == 0)
{
return x_348;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_348, 0);
x_392 = lean_ctor_get(x_348, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_348);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
else
{
uint8_t x_394; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_394 = !lean_is_exclusive(x_344);
if (x_394 == 0)
{
return x_344;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_344, 0);
x_396 = lean_ctor_get(x_344, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_344);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
return x_397;
}
}
}
case 8:
{
lean_object* x_398; 
lean_dec(x_8);
lean_inc(x_2);
x_398 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
x_400 = lean_unsigned_to_nat(0u);
x_401 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_400);
lean_inc(x_2);
x_402 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_399);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_439; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
lean_dec(x_402);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
lean_dec(x_403);
x_407 = lean_ctor_get(x_404, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
lean_dec(x_404);
x_439 = lean_unbox(x_408);
if (x_439 == 0)
{
lean_object* x_440; 
x_440 = lean_array_get_size(x_7);
x_409 = x_440;
goto block_438;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_array_get_size(x_7);
x_442 = lean_unsigned_to_nat(1u);
x_443 = lean_nat_sub(x_441, x_442);
lean_dec(x_441);
x_409 = x_443;
goto block_438;
}
block_438:
{
uint8_t x_410; 
x_410 = lean_nat_dec_lt(x_407, x_409);
if (x_410 == 0)
{
lean_object* x_411; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_411 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_406, x_9, x_10, x_11, x_12, x_405);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_Expr_getAppNumArgsAux___main(x_412, x_400);
x_415 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_414);
x_416 = lean_mk_array(x_414, x_415);
x_417 = lean_unsigned_to_nat(1u);
x_418 = lean_nat_sub(x_414, x_417);
lean_dec(x_414);
x_419 = lean_unbox(x_408);
lean_dec(x_408);
x_420 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_401, x_407, x_419, x_409, x_412, x_416, x_418, x_9, x_10, x_11, x_12, x_413);
return x_420;
}
else
{
uint8_t x_421; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_401);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_421 = !lean_is_exclusive(x_411);
if (x_421 == 0)
{
return x_411;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_411, 0);
x_423 = lean_ctor_get(x_411, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_411);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
lean_dec(x_409);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_401);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_425 = l_System_FilePath_dirName___closed__1;
x_426 = l_Lean_Name_toStringWithSep___main(x_425, x_2);
x_427 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_428 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_428, 0, x_427);
x_429 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_430 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_432 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_432, x_9, x_10, x_11, x_12, x_405);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_434 = !lean_is_exclusive(x_433);
if (x_434 == 0)
{
return x_433;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_433, 0);
x_436 = lean_ctor_get(x_433, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_433);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_401);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_444 = !lean_is_exclusive(x_402);
if (x_444 == 0)
{
return x_402;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_402, 0);
x_446 = lean_ctor_get(x_402, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_402);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_398);
if (x_448 == 0)
{
return x_398;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_398, 0);
x_450 = lean_ctor_get(x_398, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_398);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
case 9:
{
lean_object* x_452; 
lean_dec(x_8);
lean_inc(x_2);
x_452 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_unsigned_to_nat(0u);
x_455 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_454);
lean_inc(x_2);
x_456 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_453);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_493; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_456, 1);
lean_inc(x_459);
lean_dec(x_456);
x_460 = lean_ctor_get(x_457, 0);
lean_inc(x_460);
lean_dec(x_457);
x_461 = lean_ctor_get(x_458, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_458, 1);
lean_inc(x_462);
lean_dec(x_458);
x_493 = lean_unbox(x_462);
if (x_493 == 0)
{
lean_object* x_494; 
x_494 = lean_array_get_size(x_7);
x_463 = x_494;
goto block_492;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_array_get_size(x_7);
x_496 = lean_unsigned_to_nat(1u);
x_497 = lean_nat_sub(x_495, x_496);
lean_dec(x_495);
x_463 = x_497;
goto block_492;
}
block_492:
{
uint8_t x_464; 
x_464 = lean_nat_dec_lt(x_461, x_463);
if (x_464 == 0)
{
lean_object* x_465; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_465 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_460, x_9, x_10, x_11, x_12, x_459);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = l_Lean_Expr_getAppNumArgsAux___main(x_466, x_454);
x_469 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_468);
x_470 = lean_mk_array(x_468, x_469);
x_471 = lean_unsigned_to_nat(1u);
x_472 = lean_nat_sub(x_468, x_471);
lean_dec(x_468);
x_473 = lean_unbox(x_462);
lean_dec(x_462);
x_474 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_455, x_461, x_473, x_463, x_466, x_470, x_472, x_9, x_10, x_11, x_12, x_467);
return x_474;
}
else
{
uint8_t x_475; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_455);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_465);
if (x_475 == 0)
{
return x_465;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_465, 0);
x_477 = lean_ctor_get(x_465, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_465);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_455);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_479 = l_System_FilePath_dirName___closed__1;
x_480 = l_Lean_Name_toStringWithSep___main(x_479, x_2);
x_481 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_482 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_482, 0, x_481);
x_483 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_484 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_482);
x_485 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_486 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
x_487 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_486, x_9, x_10, x_11, x_12, x_459);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_488 = !lean_is_exclusive(x_487);
if (x_488 == 0)
{
return x_487;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_487, 0);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_487);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
}
else
{
uint8_t x_498; 
lean_dec(x_455);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_498 = !lean_is_exclusive(x_456);
if (x_498 == 0)
{
return x_456;
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_456, 0);
x_500 = lean_ctor_get(x_456, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_456);
x_501 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_501, 0, x_499);
lean_ctor_set(x_501, 1, x_500);
return x_501;
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_452);
if (x_502 == 0)
{
return x_452;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_452, 0);
x_504 = lean_ctor_get(x_452, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_452);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
case 10:
{
lean_object* x_506; 
lean_dec(x_8);
lean_inc(x_2);
x_506 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
lean_dec(x_506);
x_508 = lean_unsigned_to_nat(0u);
x_509 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_508);
lean_inc(x_2);
x_510 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_507);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_547; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_510, 1);
lean_inc(x_513);
lean_dec(x_510);
x_514 = lean_ctor_get(x_511, 0);
lean_inc(x_514);
lean_dec(x_511);
x_515 = lean_ctor_get(x_512, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_512, 1);
lean_inc(x_516);
lean_dec(x_512);
x_547 = lean_unbox(x_516);
if (x_547 == 0)
{
lean_object* x_548; 
x_548 = lean_array_get_size(x_7);
x_517 = x_548;
goto block_546;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_array_get_size(x_7);
x_550 = lean_unsigned_to_nat(1u);
x_551 = lean_nat_sub(x_549, x_550);
lean_dec(x_549);
x_517 = x_551;
goto block_546;
}
block_546:
{
uint8_t x_518; 
x_518 = lean_nat_dec_lt(x_515, x_517);
if (x_518 == 0)
{
lean_object* x_519; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_519 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_514, x_9, x_10, x_11, x_12, x_513);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = l_Lean_Expr_getAppNumArgsAux___main(x_520, x_508);
x_523 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_522);
x_524 = lean_mk_array(x_522, x_523);
x_525 = lean_unsigned_to_nat(1u);
x_526 = lean_nat_sub(x_522, x_525);
lean_dec(x_522);
x_527 = lean_unbox(x_516);
lean_dec(x_516);
x_528 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_509, x_515, x_527, x_517, x_520, x_524, x_526, x_9, x_10, x_11, x_12, x_521);
return x_528;
}
else
{
uint8_t x_529; 
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_509);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_529 = !lean_is_exclusive(x_519);
if (x_529 == 0)
{
return x_519;
}
else
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_519, 0);
x_531 = lean_ctor_get(x_519, 1);
lean_inc(x_531);
lean_inc(x_530);
lean_dec(x_519);
x_532 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_532, 0, x_530);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_509);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_533 = l_System_FilePath_dirName___closed__1;
x_534 = l_Lean_Name_toStringWithSep___main(x_533, x_2);
x_535 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_535, 0, x_534);
x_536 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_536, 0, x_535);
x_537 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_538 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_536);
x_539 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_540 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
x_541 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_540, x_9, x_10, x_11, x_12, x_513);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_542 = !lean_is_exclusive(x_541);
if (x_542 == 0)
{
return x_541;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_541, 0);
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_541);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_509);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_552 = !lean_is_exclusive(x_510);
if (x_552 == 0)
{
return x_510;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_510, 0);
x_554 = lean_ctor_get(x_510, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_510);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_556 = !lean_is_exclusive(x_506);
if (x_556 == 0)
{
return x_506;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_506, 0);
x_558 = lean_ctor_get(x_506, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_506);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
case 11:
{
lean_object* x_560; 
lean_dec(x_8);
lean_inc(x_2);
x_560 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_562 = lean_unsigned_to_nat(0u);
x_563 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_562);
lean_inc(x_2);
x_564 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_561);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_601; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_565, 1);
lean_inc(x_566);
x_567 = lean_ctor_get(x_564, 1);
lean_inc(x_567);
lean_dec(x_564);
x_568 = lean_ctor_get(x_565, 0);
lean_inc(x_568);
lean_dec(x_565);
x_569 = lean_ctor_get(x_566, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_566, 1);
lean_inc(x_570);
lean_dec(x_566);
x_601 = lean_unbox(x_570);
if (x_601 == 0)
{
lean_object* x_602; 
x_602 = lean_array_get_size(x_7);
x_571 = x_602;
goto block_600;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_array_get_size(x_7);
x_604 = lean_unsigned_to_nat(1u);
x_605 = lean_nat_sub(x_603, x_604);
lean_dec(x_603);
x_571 = x_605;
goto block_600;
}
block_600:
{
uint8_t x_572; 
x_572 = lean_nat_dec_lt(x_569, x_571);
if (x_572 == 0)
{
lean_object* x_573; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_573 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_568, x_9, x_10, x_11, x_12, x_567);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; lean_object* x_582; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = l_Lean_Expr_getAppNumArgsAux___main(x_574, x_562);
x_577 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_576);
x_578 = lean_mk_array(x_576, x_577);
x_579 = lean_unsigned_to_nat(1u);
x_580 = lean_nat_sub(x_576, x_579);
lean_dec(x_576);
x_581 = lean_unbox(x_570);
lean_dec(x_570);
x_582 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_563, x_569, x_581, x_571, x_574, x_578, x_580, x_9, x_10, x_11, x_12, x_575);
return x_582;
}
else
{
uint8_t x_583; 
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_563);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_573);
if (x_583 == 0)
{
return x_573;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_573, 0);
x_585 = lean_ctor_get(x_573, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_573);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_563);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_587 = l_System_FilePath_dirName___closed__1;
x_588 = l_Lean_Name_toStringWithSep___main(x_587, x_2);
x_589 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_589, 0, x_588);
x_590 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_590, 0, x_589);
x_591 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_592 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_590);
x_593 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_594 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
x_595 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_594, x_9, x_10, x_11, x_12, x_567);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_596 = !lean_is_exclusive(x_595);
if (x_596 == 0)
{
return x_595;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_595, 0);
x_598 = lean_ctor_get(x_595, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_595);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_563);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_606 = !lean_is_exclusive(x_564);
if (x_606 == 0)
{
return x_564;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_564, 0);
x_608 = lean_ctor_get(x_564, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_564);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
else
{
uint8_t x_610; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_610 = !lean_is_exclusive(x_560);
if (x_610 == 0)
{
return x_560;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_560, 0);
x_612 = lean_ctor_get(x_560, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_560);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
default: 
{
lean_object* x_614; 
lean_dec(x_8);
lean_inc(x_2);
x_614 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_6, x_7, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
x_616 = lean_unsigned_to_nat(0u);
x_617 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_5, x_6, x_616);
lean_inc(x_2);
x_618 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_4, x_5, x_6, x_7, x_9, x_10, x_11, x_12, x_615);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_655; 
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
x_621 = lean_ctor_get(x_618, 1);
lean_inc(x_621);
lean_dec(x_618);
x_622 = lean_ctor_get(x_619, 0);
lean_inc(x_622);
lean_dec(x_619);
x_623 = lean_ctor_get(x_620, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_620, 1);
lean_inc(x_624);
lean_dec(x_620);
x_655 = lean_unbox(x_624);
if (x_655 == 0)
{
lean_object* x_656; 
x_656 = lean_array_get_size(x_7);
x_625 = x_656;
goto block_654;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_array_get_size(x_7);
x_658 = lean_unsigned_to_nat(1u);
x_659 = lean_nat_sub(x_657, x_658);
lean_dec(x_657);
x_625 = x_659;
goto block_654;
}
block_654:
{
uint8_t x_626; 
x_626 = lean_nat_dec_lt(x_623, x_625);
if (x_626 == 0)
{
lean_object* x_627; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_627 = l_Lean_Meta_inferType___at___private_Lean_Meta_InferType_1__inferAppType___spec__1(x_622, x_9, x_10, x_11, x_12, x_621);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; lean_object* x_636; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
x_630 = l_Lean_Expr_getAppNumArgsAux___main(x_628, x_616);
x_631 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_630);
x_632 = lean_mk_array(x_630, x_631);
x_633 = lean_unsigned_to_nat(1u);
x_634 = lean_nat_sub(x_630, x_633);
lean_dec(x_630);
x_635 = lean_unbox(x_624);
lean_dec(x_624);
x_636 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_617, x_623, x_635, x_625, x_628, x_632, x_634, x_9, x_10, x_11, x_12, x_629);
return x_636;
}
else
{
uint8_t x_637; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_617);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_627);
if (x_637 == 0)
{
return x_627;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_627, 0);
x_639 = lean_ctor_get(x_627, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_627);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; uint8_t x_650; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_617);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_641 = l_System_FilePath_dirName___closed__1;
x_642 = l_Lean_Name_toStringWithSep___main(x_641, x_2);
x_643 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_646 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_644);
x_647 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_648 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_648, x_9, x_10, x_11, x_12, x_621);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_650 = !lean_is_exclusive(x_649);
if (x_650 == 0)
{
return x_649;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_649, 0);
x_652 = lean_ctor_get(x_649, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_649);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_617);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_618);
if (x_660 == 0)
{
return x_618;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_618, 0);
x_662 = lean_ctor_get(x_618, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_618);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
else
{
uint8_t x_664; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_664 = !lean_is_exclusive(x_614);
if (x_664 == 0)
{
return x_614;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_614, 0);
x_666 = lean_ctor_get(x_614, 1);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_614);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_12);
x_14 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
x_18 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_17, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_8);
x_9 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_ConstantInfo_type(x_1);
x_13 = l___private_Lean_Meta_Basic_12__withNewLocalInstancesImp___main___rarg___closed__3;
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed), 11, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_8);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_10);
x_15 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNamesImp___spec__3___rarg(x_12, x_14, x_3, x_4, x_5, x_6, x_11);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; lean_object* x_22; 
x_21 = lean_unbox(x_11);
lean_dec(x_11);
x_22 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_3);
return x_20;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object** _args) {
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
lean_object* x_18 = _args[17];
_start:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_unbox(x_8);
lean_dec(x_8);
x_20 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
return x_20;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of argument");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise position must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_Syntax_inhabited;
x_7 = lean_array_get(x_6, x_2, x_4);
x_8 = l_Lean_numLitKind;
x_9 = l_Lean_Syntax_isNatLitAux(x_8, x_7);
lean_dec(x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_11, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4;
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
return x_18;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_11, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_9, x_2, x_3, x_4, x_5, x_6, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__5___rarg(x_7, x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
}
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
lean_object* _init_l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_inhabited;
x_2 = l_Nat_Inhabited;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_swap(x_3, x_4, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
x_10 = lean_array_get(x_9, x_3, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
x_13 = l_Lean_Name_quickLt(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_3, x_4, x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_20 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_3 = x_17;
x_4 = x_19;
x_5 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_42 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
x_43 = lean_array_get(x_42, x_1, x_16);
x_44 = lean_array_get(x_42, x_1, x_2);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Name_quickLt(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
x_17 = x_1;
goto block_41;
}
else
{
lean_object* x_48; 
x_48 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_48;
goto block_41;
}
block_41:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Name_quickLt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get(x_18, x_17, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_quickLt(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_27 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_19, x_17, x_2, x_2);
lean_dec(x_19);
x_4 = x_27;
goto block_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
x_28 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_29 = lean_array_get(x_18, x_28, x_3);
lean_inc_n(x_2, 2);
x_30 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_29, x_28, x_2, x_2);
lean_dec(x_29);
x_4 = x_30;
goto block_12;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_19);
x_31 = lean_array_swap(x_17, x_2, x_3);
x_32 = lean_array_get(x_18, x_31, x_16);
x_33 = lean_array_get(x_18, x_31, x_3);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = l_Lean_Name_quickLt(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_16);
lean_inc_n(x_2, 2);
x_37 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_33, x_31, x_2, x_2);
lean_dec(x_33);
x_4 = x_37;
goto block_12;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_38 = lean_array_swap(x_31, x_16, x_3);
lean_dec(x_16);
x_39 = lean_array_get(x_18, x_38, x_3);
lean_inc_n(x_2, 2);
x_40 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_39, x_38, x_2, x_2);
lean_dec(x_39);
x_4 = x_40;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_name_eq(x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_5);
return x_11;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(x_1, x_6, x_6, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_free_object(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_18 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_18, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
lean_ctor_set(x_22, 5, x_16);
x_23 = lean_st_ref_take(x_3, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_st_ref_set(x_3, x_27, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_22);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = l_System_FilePath_dirName___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_37);
x_40 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_registerInternalExceptionId___closed__2;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(x_1, x_45, x_45, x_47, x_48);
lean_dec(x_47);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 2);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 3);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 4);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 5);
lean_inc(x_55);
lean_dec(x_1);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_57 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_57, 0, x_51);
lean_closure_set(x_57, 1, x_56);
x_58 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_57, x_46);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_50);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_55);
x_62 = lean_st_ref_take(x_3, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_61);
x_65 = x_61;
x_66 = lean_array_push(x_63, x_65);
x_67 = lean_st_ref_set(x_3, x_66, x_64);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
lean_dec(x_1);
x_76 = l_System_FilePath_dirName___closed__1;
x_77 = l_Lean_Name_toStringWithSep___main(x_76, x_75);
x_78 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lean_registerInternalExceptionId___closed__2;
x_81 = lean_string_append(x_79, x_80);
x_82 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_46);
return x_83;
}
}
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_2, x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_3, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* _init_l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_registerParametricAttribute___rarg___closed__1;
x_8 = l_Lean_registerParametricAttribute___rarg___closed__2;
x_9 = l_Lean_registerParametricAttribute___rarg___closed__3;
x_10 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1;
x_11 = l_Lean_registerParametricAttribute___rarg___closed__4;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___rarg___lambda__5___boxed), 10, 4);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_1);
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_inc(x_17);
x_18 = l_Lean_registerBuiltinAttribute(x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_13);
if (x_29 == 0)
{
return x_13;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_13, 0);
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_13);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(x_2);
x_7 = l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(x_6, x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lean_Meta_State_inhabited___closed__7;
x_8 = lean_st_mk_ref(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_inc(x_9);
x_12 = l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(x_1, x_6, x_11, x_9, x_3, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_st_ref_get(x_9, x_13);
lean_dec(x_9);
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
uint8_t x_21; 
lean_dec(x_9);
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
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursor");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkRecursorAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("user defined recursor, numerical parameter specifies position of the major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorAttr___lambda__2), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_2 = l_Lean_Meta_mkRecursorAttr___closed__2;
x_3 = l_Lean_Meta_mkRecursorAttr___closed__3;
x_4 = l_Lean_Meta_mkRecursorAttr___closed__4;
x_5 = l_Lean_Meta_mkRecursorAttr___closed__5;
x_6 = 0;
x_7 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkRecursorAttr___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_Std_RBNode_find___main___at_Lean_LocalContext_sanitizeNames___spec__1(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_array_get_size(x_10);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_10, x_12, x_11, x_15);
lean_dec(x_12);
lean_dec(x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_recursorAttribute;
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Meta_getMajorPos_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getMajorPos_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_getParamNamesImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
lean_dec(x_9);
x_21 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_20, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_11 = x_22;
goto block_19;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_23;
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_12 = lean_st_ref_get(x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_recursorAttribute;
x_17 = l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(x_16, x_15, x_1);
lean_dec(x_15);
x_18 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_9, x_17, x_3, x_4, x_5, x_6, x_14);
return x_18;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_RecursorInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_casesOnSuffix___closed__1 = _init_l_Lean_Meta_casesOnSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_casesOnSuffix___closed__1);
l_Lean_Meta_casesOnSuffix = _init_l_Lean_Meta_casesOnSuffix();
lean_mark_persistent(l_Lean_Meta_casesOnSuffix);
l_Lean_Meta_recOnSuffix___closed__1 = _init_l_Lean_Meta_recOnSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_recOnSuffix___closed__1);
l_Lean_Meta_recOnSuffix = _init_l_Lean_Meta_recOnSuffix();
lean_mark_persistent(l_Lean_Meta_recOnSuffix);
l_Lean_Meta_brecOnSuffix___closed__1 = _init_l_Lean_Meta_brecOnSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_brecOnSuffix___closed__1);
l_Lean_Meta_brecOnSuffix = _init_l_Lean_Meta_brecOnSuffix();
lean_mark_persistent(l_Lean_Meta_brecOnSuffix);
l_Lean_Meta_binductionOnSuffix___closed__1 = _init_l_Lean_Meta_binductionOnSuffix___closed__1();
lean_mark_persistent(l_Lean_Meta_binductionOnSuffix___closed__1);
l_Lean_Meta_binductionOnSuffix = _init_l_Lean_Meta_binductionOnSuffix();
lean_mark_persistent(l_Lean_Meta_binductionOnSuffix);
l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1 = _init_l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1();
lean_mark_persistent(l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1);
l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1 = _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1();
lean_mark_persistent(l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1);
l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1 = _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1();
lean_mark_persistent(l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1);
l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1 = _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1();
lean_mark_persistent(l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1);
l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2 = _init_l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2();
lean_mark_persistent(l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2);
l_Lean_Meta_RecursorInfo_HasToString___closed__1 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__1();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__1);
l_Lean_Meta_RecursorInfo_HasToString___closed__2 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__2();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__2);
l_Lean_Meta_RecursorInfo_HasToString___closed__3 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__3();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__3);
l_Lean_Meta_RecursorInfo_HasToString___closed__4 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__4();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__4);
l_Lean_Meta_RecursorInfo_HasToString___closed__5 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__5();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__5);
l_Lean_Meta_RecursorInfo_HasToString___closed__6 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__6();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__6);
l_Lean_Meta_RecursorInfo_HasToString___closed__7 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__7();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__7);
l_Lean_Meta_RecursorInfo_HasToString___closed__8 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__8();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__8);
l_Lean_Meta_RecursorInfo_HasToString___closed__9 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__9();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__9);
l_Lean_Meta_RecursorInfo_HasToString___closed__10 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__10();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__10);
l_Lean_Meta_RecursorInfo_HasToString___closed__11 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__11();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__11);
l_Lean_Meta_RecursorInfo_HasToString___closed__12 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__12();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__12);
l_Lean_Meta_RecursorInfo_HasToString___closed__13 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__13();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__13);
l_Lean_Meta_RecursorInfo_HasToString___closed__14 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__14();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__14);
l_Lean_Meta_RecursorInfo_HasToString___closed__15 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__15();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__15);
l_Lean_Meta_RecursorInfo_HasToString___closed__16 = _init_l_Lean_Meta_RecursorInfo_HasToString___closed__16();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_HasToString___closed__16);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8);
l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9 = _init_l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__1);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__2);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___lambda__1___closed__3);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__1);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__2);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___lambda__1___closed__3);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__1);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__2);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___lambda__1___closed__3);
l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__5);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8);
l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9 = _init_l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4);
l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1 = _init_l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_1__qpartitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1);
l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1 = _init_l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1();
lean_mark_persistent(l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1);
l_Lean_Meta_mkRecursorAttr___closed__1 = _init_l_Lean_Meta_mkRecursorAttr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___closed__1);
l_Lean_Meta_mkRecursorAttr___closed__2 = _init_l_Lean_Meta_mkRecursorAttr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___closed__2);
l_Lean_Meta_mkRecursorAttr___closed__3 = _init_l_Lean_Meta_mkRecursorAttr___closed__3();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___closed__3);
l_Lean_Meta_mkRecursorAttr___closed__4 = _init_l_Lean_Meta_mkRecursorAttr___closed__4();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___closed__4);
l_Lean_Meta_mkRecursorAttr___closed__5 = _init_l_Lean_Meta_mkRecursorAttr___closed__5();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___closed__5);
res = l_Lean_Meta_mkRecursorAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recursorAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recursorAttribute);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
