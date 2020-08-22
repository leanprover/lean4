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
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_brecOnSuffix___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object**);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__4;
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(lean_object*);
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_back___at___private_Lean_Meta_ExprDefEq_15__processAssignmentFOApproxAux___spec__1(lean_object*);
lean_object* lean_io_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__14;
lean_object* l_Lean_Meta_recOnSuffix;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__5;
lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
lean_object* l_Lean_Core_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* lean_io_ref_take(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__8;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__4;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
extern lean_object* l_IO_FS_Handle_putStrLn___rarg___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__13;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__1;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object**);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7___boxed(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__4;
lean_object* l_Lean_Meta_RecursorInfo_HasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18;
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_Lean_Meta_mkRecOnFor(lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__2;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__1;
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__2;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__9;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__3(lean_object*);
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
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
lean_object* l_Lean_Meta_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__11;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__1(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__12;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__16;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(uint8_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object**);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__10;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__15;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__3;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2;
lean_object* l_Lean_Meta_recOnSuffix___closed__1;
extern lean_object* l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2;
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
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_Name_toStringWithSep___main(x_3, x_2);
x_5 = l_Lean_Meta_RecursorInfo_HasToString___closed__3;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_IO_FS_Handle_putStrLn___rarg___closed__1;
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
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
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
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_6);
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
x_12 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed builtin recursor");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_RecursorVal_getInduct(x_2);
lean_inc(x_8);
x_9 = l_Lean_Meta_getConstInfo(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_List_lengthAux___main___rarg(x_15, x_16);
lean_dec(x_15);
lean_inc(x_17);
x_18 = l_List_range(x_17);
x_19 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_18);
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_List_lengthAux___main___rarg(x_21, x_16);
lean_dec(x_21);
x_23 = lean_nat_dec_eq(x_22, x_17);
lean_dec(x_17);
lean_dec(x_22);
x_24 = lean_ctor_get(x_2, 5);
lean_inc(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
lean_inc(x_24);
x_27 = l_List_replicate___rarg(x_24, x_26);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_inc(x_28);
x_29 = l_List_range(x_28);
x_30 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_29);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
lean_inc(x_31);
x_32 = l_List_range(x_31);
x_33 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_28, x_32);
x_34 = lean_nat_add(x_31, x_28);
lean_dec(x_28);
lean_dec(x_31);
x_35 = lean_nat_add(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
x_36 = lean_ctor_get(x_2, 4);
lean_inc(x_36);
x_37 = lean_nat_add(x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_37, x_38);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_13, sizeof(void*)*5);
lean_dec(x_13);
x_41 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_23 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_19);
x_44 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_8);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_39);
lean_ctor_set(x_44, 4, x_41);
lean_ctor_set(x_44, 5, x_30);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_27);
lean_ctor_set_uint8(x_44, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_44, sizeof(void*)*8 + 1, x_40);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_8);
lean_ctor_set(x_45, 2, x_19);
lean_ctor_set(x_45, 3, x_39);
lean_ctor_set(x_45, 4, x_41);
lean_ctor_set(x_45, 5, x_30);
lean_ctor_set(x_45, 6, x_33);
lean_ctor_set(x_45, 7, x_27);
lean_ctor_set_uint8(x_45, sizeof(void*)*8, x_25);
lean_ctor_set_uint8(x_45, sizeof(void*)*8 + 1, x_40);
lean_ctor_set(x_9, 0, x_45);
return x_9;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_46 = lean_ctor_get(x_9, 1);
lean_inc(x_46);
lean_dec(x_9);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
lean_dec(x_10);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_List_lengthAux___main___rarg(x_49, x_50);
lean_dec(x_49);
lean_inc(x_51);
x_52 = l_List_range(x_51);
x_53 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_52);
x_54 = lean_ctor_get(x_2, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_List_lengthAux___main___rarg(x_55, x_50);
lean_dec(x_55);
x_57 = lean_nat_dec_eq(x_56, x_51);
lean_dec(x_51);
lean_dec(x_56);
x_58 = lean_ctor_get(x_2, 5);
lean_inc(x_58);
x_59 = 1;
x_60 = lean_box(x_59);
lean_inc(x_58);
x_61 = l_List_replicate___rarg(x_58, x_60);
x_62 = lean_ctor_get(x_2, 2);
lean_inc(x_62);
lean_inc(x_62);
x_63 = l_List_range(x_62);
x_64 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_63);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_65);
lean_inc(x_65);
x_66 = l_List_range(x_65);
x_67 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_62, x_66);
x_68 = lean_nat_add(x_65, x_62);
lean_dec(x_62);
lean_dec(x_65);
x_69 = lean_nat_add(x_68, x_58);
lean_dec(x_58);
lean_dec(x_68);
x_70 = lean_ctor_get(x_2, 4);
lean_inc(x_70);
x_71 = lean_nat_add(x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_71, x_72);
lean_dec(x_71);
x_74 = lean_ctor_get_uint8(x_47, sizeof(void*)*5);
lean_dec(x_47);
x_75 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_57 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_53);
x_78 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_8);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_75);
lean_ctor_set(x_78, 5, x_64);
lean_ctor_set(x_78, 6, x_67);
lean_ctor_set(x_78, 7, x_61);
lean_ctor_set_uint8(x_78, sizeof(void*)*8, x_59);
lean_ctor_set_uint8(x_78, sizeof(void*)*8 + 1, x_74);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_46);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_8);
lean_ctor_set(x_80, 2, x_53);
lean_ctor_set(x_80, 3, x_73);
lean_ctor_set(x_80, 4, x_75);
lean_ctor_set(x_80, 5, x_64);
lean_ctor_set(x_80, 6, x_67);
lean_ctor_set(x_80, 7, x_61);
lean_ctor_set_uint8(x_80, sizeof(void*)*8, x_59);
lean_ctor_set_uint8(x_80, sizeof(void*)*8 + 1, x_74);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_46);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_9, 1);
lean_inc(x_82);
lean_dec(x_9);
x_83 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
x_84 = l_Lean_Meta_throwError___rarg(x_83, x_3, x_4, x_5, x_6, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_9);
if (x_85 == 0)
{
return x_9;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_9, 0);
x_87 = lean_ctor_get(x_9, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_9);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_2);
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
lean_object* _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected recursor information");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Core_getEnv___rarg(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_auxRecExt;
x_13 = l_Lean_TagDeclarationExtension_isTagged(x_12, x_10, x_1);
lean_dec(x_10);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_59; uint8_t x_60; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_59 = l_Lean_Meta_recOnSuffix;
x_60 = lean_string_dec_eq(x_16, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Meta_casesOnSuffix;
x_62 = lean_string_dec_eq(x_16, x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Meta_brecOnSuffix;
x_64 = lean_string_dec_eq(x_16, x_63);
if (x_64 == 0)
{
lean_object* x_65; 
lean_dec(x_16);
lean_dec(x_15);
x_65 = lean_box(0);
lean_ctor_set(x_8, 0, x_65);
return x_8;
}
else
{
lean_object* x_66; 
lean_free_object(x_8);
x_66 = lean_box(0);
x_17 = x_66;
goto block_58;
}
}
else
{
lean_object* x_67; 
lean_free_object(x_8);
x_67 = lean_box(0);
x_17 = x_67;
goto block_58;
}
}
else
{
lean_object* x_68; 
lean_free_object(x_8);
x_68 = lean_box(0);
x_17 = x_68;
goto block_58;
}
block_58:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = l_Lean_mkRecFor___closed__1;
x_19 = lean_name_mk_string(x_15, x_18);
x_20 = l_Lean_Meta_getConstInfo(x_19, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 7)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 3);
lean_inc(x_26);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_26);
lean_dec(x_25);
x_28 = l_Lean_Meta_casesOnSuffix;
x_29 = lean_string_dec_eq(x_16, x_28);
lean_dec(x_16);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 4);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_nat_add(x_27, x_30);
lean_dec(x_30);
lean_dec(x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_27, x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_20, 0, x_35);
return x_20;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 3);
lean_inc(x_39);
x_40 = lean_nat_add(x_38, x_39);
lean_dec(x_39);
lean_dec(x_38);
x_41 = l_Lean_Meta_casesOnSuffix;
x_42 = lean_string_dec_eq(x_16, x_41);
lean_dec(x_16);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_37, 4);
lean_inc(x_43);
lean_dec(x_37);
x_44 = lean_nat_add(x_40, x_43);
lean_dec(x_43);
lean_dec(x_40);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_36);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_40, x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_36);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_21);
lean_dec(x_16);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_dec(x_20);
x_52 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
x_53 = l_Lean_Meta_throwError___rarg(x_52, x_3, x_4, x_5, x_6, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
x_54 = !lean_is_exclusive(x_20);
if (x_54 == 0)
{
return x_20;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_20, 0);
x_56 = lean_ctor_get(x_20, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_20);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_1);
x_69 = lean_box(0);
lean_ctor_set(x_8, 0, x_69);
return x_8;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_8, 0);
x_71 = lean_ctor_get(x_8, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_8);
x_72 = l_Lean_auxRecExt;
x_73 = l_Lean_TagDeclarationExtension_isTagged(x_72, x_70, x_1);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_107; uint8_t x_108; 
x_76 = lean_ctor_get(x_1, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_1, 1);
lean_inc(x_77);
lean_dec(x_1);
x_107 = l_Lean_Meta_recOnSuffix;
x_108 = lean_string_dec_eq(x_77, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = l_Lean_Meta_casesOnSuffix;
x_110 = lean_string_dec_eq(x_77, x_109);
if (x_110 == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = l_Lean_Meta_brecOnSuffix;
x_112 = lean_string_dec_eq(x_77, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_77);
lean_dec(x_76);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_71);
return x_114;
}
else
{
lean_object* x_115; 
x_115 = lean_box(0);
x_78 = x_115;
goto block_106;
}
}
else
{
lean_object* x_116; 
x_116 = lean_box(0);
x_78 = x_116;
goto block_106;
}
}
else
{
lean_object* x_117; 
x_117 = lean_box(0);
x_78 = x_117;
goto block_106;
}
block_106:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_78);
x_79 = l_Lean_mkRecFor___closed__1;
x_80 = lean_name_mk_string(x_76, x_79);
x_81 = l_Lean_Meta_getConstInfo(x_80, x_3, x_4, x_5, x_6, x_71);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 7)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_ctor_get(x_85, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 3);
lean_inc(x_87);
x_88 = lean_nat_add(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
x_89 = l_Lean_Meta_casesOnSuffix;
x_90 = lean_string_dec_eq(x_77, x_89);
lean_dec(x_77);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 4);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_nat_add(x_88, x_91);
lean_dec(x_91);
lean_dec(x_88);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_84)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_84;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_83);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_85);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_add(x_88, x_95);
lean_dec(x_88);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_84)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_84;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_83);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_82);
lean_dec(x_77);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_dec(x_81);
x_100 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
x_101 = l_Lean_Meta_throwError___rarg(x_100, x_3, x_4, x_5, x_6, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_77);
x_102 = lean_ctor_get(x_81, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_81, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_104 = x_81;
} else {
 lean_dec_ref(x_81);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_71);
return x_119;
}
}
}
}
else
{
lean_object* x_120; 
lean_dec(x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_2);
lean_ctor_set(x_120, 1, x_7);
return x_120;
}
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
uint8_t x_9; 
x_9 = l_Lean_Expr_isFVar(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = l_Lean_Name_toString___closed__1;
x_11 = l_Lean_Name_toStringWithSep___main(x_10, x_1);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_throwError___rarg(x_19, x_4, x_5, x_6, x_7, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_array_get_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_3, x_3, x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_throwError___rarg(x_35, x_4, x_5, x_6, x_7, x_8);
return x_36;
}
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
x_12 = l_Array_back___at___private_Lean_Meta_ExprDefEq_15__processAssignmentFOApproxAux___spec__1(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_12, x_3, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Core_getConstInfo___closed__5;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_throwError___rarg(x_22, x_6, x_7, x_8, x_9, x_10);
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
x_30 = l_Lean_Name_toString___closed__1;
x_31 = l_Lean_Name_toStringWithSep___main(x_30, x_1);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_throwError___rarg(x_41, x_6, x_7, x_8, x_9, x_10);
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
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Meta_throwError___rarg(x_56, x_6, x_7, x_8, x_9, x_10);
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
x_14 = l_Lean_Meta_isExprDefEq(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor parameter");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = lean_nat_sub(x_16, x_14);
lean_dec(x_16);
x_18 = l_Lean_Expr_Inhabited;
x_19 = lean_array_get(x_18, x_2, x_17);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_19);
x_20 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_19, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_fvarId_x21(x_19);
lean_dec(x_19);
lean_inc(x_7);
x_24 = l_Lean_Meta_getLocalDecl(x_23, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_binderInfo(x_25);
lean_dec(x_25);
x_28 = l_Lean_BinderInfo_isInstImplicit(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_15);
lean_dec(x_6);
x_29 = l_Lean_Name_toString___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_1);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_throwError___rarg(x_36, x_7, x_8, x_9, x_10, x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; 
x_42 = lean_array_push(x_6, x_21);
x_5 = x_15;
x_6 = x_42;
x_11 = x_26;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
return x_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_19);
x_48 = lean_ctor_get(x_20, 1);
lean_inc(x_48);
lean_dec(x_20);
x_49 = lean_array_push(x_6, x_21);
x_5 = x_15;
x_6 = x_49;
x_11 = x_48;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_6);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
lean_inc(x_3);
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_4, x_3, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Array_toList___rarg(x_13);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l_Array_toList___rarg(x_15);
lean_dec(x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
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
x_14 = l_Lean_Meta_isExprDefEq(x_13, x_1, x_4, x_5, x_6, x_7, x_8);
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor index");
return x_1;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_18 = lean_nat_sub(x_6, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = lean_nat_sub(x_3, x_4);
x_21 = lean_nat_add(x_20, x_19);
lean_dec(x_19);
lean_dec(x_20);
x_22 = l_Lean_Expr_Inhabited;
x_23 = lean_array_get(x_22, x_2, x_21);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_23, x_5, x_14, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_17);
lean_dec(x_8);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Meta_throwError___rarg(x_34, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_ctor_get(x_25, 0);
lean_inc(x_41);
lean_dec(x_25);
x_42 = lean_array_push(x_8, x_41);
x_7 = x_17;
x_8 = x_42;
x_13 = x_40;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_24);
if (x_44 == 0)
{
return x_24;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_24, 0);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_24);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_13);
return x_48;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Array_empty___closed__1;
lean_inc(x_4);
x_12 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_4, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
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
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
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
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_1);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_throwError___rarg(x_16, x_3, x_4, x_5, x_6, x_7);
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
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , major premise type does not contain universe level parameter '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
lean_inc(x_12);
x_14 = l_Lean_mkLevelParam(x_12);
x_15 = lean_level_eq(x_2, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_14, x_3, x_16);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_4);
x_18 = l_Lean_Name_toString___closed__1;
x_19 = l_Lean_Name_toStringWithSep___main(x_18, x_1);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Name_toStringWithSep___main(x_18, x_12);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Core_getConstInfo___closed__5;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Meta_throwError___rarg(x_31, x_6, x_7, x_8, x_9, x_10);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_array_push(x_4, x_38);
x_4 = x_39;
x_5 = x_13;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_14);
lean_dec(x_12);
x_41 = lean_box(0);
x_42 = lean_array_push(x_4, x_41);
x_4 = x_42;
x_5 = x_13;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_List_redLength___main___rarg(x_4);
x_11 = lean_mk_empty_array_with_capacity(x_10);
lean_dec(x_10);
x_12 = l_List_toArrayAux___main___rarg(x_4, x_11);
x_13 = l_Array_empty___closed__1;
x_14 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_3, x_12, x_13, x_2, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
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
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
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
x_16 = l_Lean_Meta_inferType(x_15, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_42; uint8_t x_43; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_18 = lean_nat_sub(x_6, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_42 = lean_nat_add(x_2, x_16);
x_43 = lean_nat_dec_lt(x_19, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_nat_sub(x_4, x_3);
x_45 = lean_nat_dec_le(x_44, x_19);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_20 = x_46;
goto block_41;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_19, x_4);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_box(0);
x_20 = x_48;
goto block_41;
}
else
{
lean_dec(x_19);
x_7 = x_17;
goto _start;
}
}
}
else
{
lean_dec(x_19);
x_7 = x_17;
goto _start;
}
block_41:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_Expr_Inhabited;
x_24 = lean_array_get(x_23, x_1, x_19);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_inferType(x_24, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_5);
x_28 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed), 10, 3);
lean_closure_set(x_28, 0, x_5);
lean_closure_set(x_28, 1, x_21);
lean_closure_set(x_28, 2, x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Meta_forallTelescopeReducing___rarg(x_26, x_28, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_7 = x_17;
x_8 = x_30;
x_13 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
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
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_37 = !lean_is_exclusive(x_25);
if (x_37 == 0)
{
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_13);
return x_51;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_1);
x_12 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_11);
x_13 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_11, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_13;
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
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_27 = x_23;
} else {
 lean_dec_ref(x_23);
 x_27 = lean_box(0);
}
x_28 = l_Array_toList___rarg(x_25);
lean_dec(x_25);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_13);
if (x_31 == 0)
{
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_13, 0);
x_33 = lean_ctor_get(x_13, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
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
uint8_t x_10; 
x_10 = l_Lean_Expr_isSort(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_1);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Meta_throwError___rarg(x_22, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get_size(x_2);
x_25 = lean_array_get_size(x_4);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_throwError___rarg(x_38, x_5, x_6, x_7, x_8, x_9);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
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
lean_inc(x_1);
x_27 = l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_26, x_24, x_4, x_16, x_17, x_18, x_19, x_25);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
switch (lean_obj_tag(x_10)) {
case 4:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_3, x_6, x_11, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_2);
x_23 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_11, x_13, x_14, x_15, x_16, x_22);
lean_dec(x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_4);
x_26 = l_Lean_Meta_inferType(x_4, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(x_8);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 20, 13);
lean_closure_set(x_30, 0, x_2);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_1);
lean_closure_set(x_30, 3, x_19);
lean_closure_set(x_30, 4, x_3);
lean_closure_set(x_30, 5, x_6);
lean_closure_set(x_30, 6, x_9);
lean_closure_set(x_30, 7, x_7);
lean_closure_set(x_30, 8, x_4);
lean_closure_set(x_30, 9, x_18);
lean_closure_set(x_30, 10, x_29);
lean_closure_set(x_30, 11, x_21);
lean_closure_set(x_30, 12, x_24);
x_31 = l_Lean_Meta_forallTelescopeReducing___rarg(x_27, x_30, x_13, x_14, x_15, x_16, x_28);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 5:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_10, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_array_set(x_11, x_12, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_12, x_47);
lean_dec(x_12);
x_10 = x_44;
x_11 = x_46;
x_12 = x_48;
goto _start;
}
default: 
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = l_Lean_Name_toString___closed__1;
x_51 = l_Lean_Name_toStringWithSep___main(x_50, x_2);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Meta_throwError___rarg(x_57, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_58;
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
lean_inc(x_6);
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
lean_inc(x_2);
x_24 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_12, x_14, x_15, x_16, x_17, x_23);
lean_dec(x_12);
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
x_27 = l_Lean_Meta_inferType(x_4, x_14, x_15, x_16, x_17, x_26);
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
x_32 = l_Lean_Meta_forallTelescopeReducing___rarg(x_28, x_31, x_14, x_15, x_16, x_17, x_29);
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
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_10);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Meta_throwError___rarg(x_52, x_14, x_15, x_16, x_17, x_18);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_7);
lean_inc(x_2);
x_13 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_15);
lean_inc(x_2);
x_17 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_54; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_54 = lean_unbox(x_23);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_array_get_size(x_6);
x_24 = x_55;
goto block_53;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_array_get_size(x_6);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_24 = x_58;
goto block_53;
}
block_53:
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Meta_inferType(x_21, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_getAppNumArgsAux___main(x_27, x_15);
x_30 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_29);
x_31 = lean_mk_array(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_29, x_32);
lean_dec(x_29);
x_34 = lean_unbox(x_23);
lean_dec(x_23);
x_35 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_16, x_22, x_34, x_24, x_27, x_31, x_33, x_8, x_9, x_10, x_11, x_28);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_40 = l_Lean_Name_toString___closed__1;
x_41 = l_Lean_Name_toStringWithSep___main(x_40, x_2);
x_42 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_throwError___rarg(x_47, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
return x_13;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_13, 0);
x_65 = lean_ctor_get(x_13, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_13);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
case 1:
{
lean_object* x_67; 
lean_dec(x_7);
lean_inc(x_2);
x_67 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_69);
lean_inc(x_2);
x_71 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_108; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_108 = lean_unbox(x_77);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_array_get_size(x_6);
x_78 = x_109;
goto block_107;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_array_get_size(x_6);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_110, x_111);
lean_dec(x_110);
x_78 = x_112;
goto block_107;
}
block_107:
{
uint8_t x_79; 
x_79 = lean_nat_dec_lt(x_76, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_80 = l_Lean_Meta_inferType(x_75, x_8, x_9, x_10, x_11, x_74);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Expr_getAppNumArgsAux___main(x_81, x_69);
x_84 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
x_88 = lean_unbox(x_77);
lean_dec(x_77);
x_89 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_70, x_76, x_88, x_78, x_81, x_85, x_87, x_8, x_9, x_10, x_11, x_82);
return x_89;
}
else
{
uint8_t x_90; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_80);
if (x_90 == 0)
{
return x_80;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_80, 0);
x_92 = lean_ctor_get(x_80, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_80);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = l_Lean_Name_toString___closed__1;
x_95 = l_Lean_Name_toStringWithSep___main(x_94, x_2);
x_96 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_throwError___rarg(x_101, x_8, x_9, x_10, x_11, x_74);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
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
return x_106;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_71);
if (x_113 == 0)
{
return x_71;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_71, 0);
x_115 = lean_ctor_get(x_71, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_71);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_67);
if (x_117 == 0)
{
return x_67;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_67, 0);
x_119 = lean_ctor_get(x_67, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_67);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
case 2:
{
lean_object* x_121; 
lean_dec(x_7);
lean_inc(x_2);
x_121 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_unsigned_to_nat(0u);
x_124 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_123);
lean_inc(x_2);
x_125 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_162; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_162 = lean_unbox(x_131);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_array_get_size(x_6);
x_132 = x_163;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_array_get_size(x_6);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_sub(x_164, x_165);
lean_dec(x_164);
x_132 = x_166;
goto block_161;
}
block_161:
{
uint8_t x_133; 
x_133 = lean_nat_dec_lt(x_130, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_134 = l_Lean_Meta_inferType(x_129, x_8, x_9, x_10, x_11, x_128);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Expr_getAppNumArgsAux___main(x_135, x_123);
x_138 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_137);
x_139 = lean_mk_array(x_137, x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_137, x_140);
lean_dec(x_137);
x_142 = lean_unbox(x_131);
lean_dec(x_131);
x_143 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_124, x_130, x_142, x_132, x_135, x_139, x_141, x_8, x_9, x_10, x_11, x_136);
return x_143;
}
else
{
uint8_t x_144; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_124);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_144 = !lean_is_exclusive(x_134);
if (x_144 == 0)
{
return x_134;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_134, 0);
x_146 = lean_ctor_get(x_134, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_134);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_124);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_148 = l_Lean_Name_toString___closed__1;
x_149 = l_Lean_Name_toStringWithSep___main(x_148, x_2);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_155 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Meta_throwError___rarg(x_155, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
return x_156;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_156);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_124);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_125);
if (x_167 == 0)
{
return x_125;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_125, 0);
x_169 = lean_ctor_get(x_125, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_125);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_121);
if (x_171 == 0)
{
return x_121;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_121, 0);
x_173 = lean_ctor_get(x_121, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_121);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
case 3:
{
lean_object* x_175; 
lean_dec(x_7);
lean_inc(x_2);
x_175 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_177);
lean_inc(x_2);
x_179 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_216; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec(x_179);
x_183 = lean_ctor_get(x_180, 0);
lean_inc(x_183);
lean_dec(x_180);
x_184 = lean_ctor_get(x_181, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_181, 1);
lean_inc(x_185);
lean_dec(x_181);
x_216 = lean_unbox(x_185);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_array_get_size(x_6);
x_186 = x_217;
goto block_215;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_array_get_size(x_6);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_sub(x_218, x_219);
lean_dec(x_218);
x_186 = x_220;
goto block_215;
}
block_215:
{
uint8_t x_187; 
x_187 = lean_nat_dec_lt(x_184, x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_188 = l_Lean_Meta_inferType(x_183, x_8, x_9, x_10, x_11, x_182);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Expr_getAppNumArgsAux___main(x_189, x_177);
x_192 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_191);
x_193 = lean_mk_array(x_191, x_192);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_sub(x_191, x_194);
lean_dec(x_191);
x_196 = lean_unbox(x_185);
lean_dec(x_185);
x_197 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_178, x_184, x_196, x_186, x_189, x_193, x_195, x_8, x_9, x_10, x_11, x_190);
return x_197;
}
else
{
uint8_t x_198; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_178);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_188);
if (x_198 == 0)
{
return x_188;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_188, 0);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_188);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_178);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_202 = l_Lean_Name_toString___closed__1;
x_203 = l_Lean_Name_toStringWithSep___main(x_202, x_2);
x_204 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_207 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_Meta_throwError___rarg(x_209, x_8, x_9, x_10, x_11, x_182);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
return x_210;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_210, 0);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_210);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_178);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_179);
if (x_221 == 0)
{
return x_179;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_179, 0);
x_223 = lean_ctor_get(x_179, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_179);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_225 = !lean_is_exclusive(x_175);
if (x_225 == 0)
{
return x_175;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_175, 0);
x_227 = lean_ctor_get(x_175, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_175);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
case 4:
{
lean_object* x_229; 
lean_dec(x_7);
lean_inc(x_2);
x_229 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_unsigned_to_nat(0u);
x_232 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_231);
lean_inc(x_2);
x_233 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_270; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
lean_dec(x_235);
x_270 = lean_unbox(x_239);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = lean_array_get_size(x_6);
x_240 = x_271;
goto block_269;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_array_get_size(x_6);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_sub(x_272, x_273);
lean_dec(x_272);
x_240 = x_274;
goto block_269;
}
block_269:
{
uint8_t x_241; 
x_241 = lean_nat_dec_lt(x_238, x_240);
if (x_241 == 0)
{
lean_object* x_242; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_242 = l_Lean_Meta_inferType(x_237, x_8, x_9, x_10, x_11, x_236);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; uint8_t x_250; lean_object* x_251; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = l_Lean_Expr_getAppNumArgsAux___main(x_243, x_231);
x_246 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_245);
x_247 = lean_mk_array(x_245, x_246);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_nat_sub(x_245, x_248);
lean_dec(x_245);
x_250 = lean_unbox(x_239);
lean_dec(x_239);
x_251 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_232, x_238, x_250, x_240, x_243, x_247, x_249, x_8, x_9, x_10, x_11, x_244);
return x_251;
}
else
{
uint8_t x_252; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_232);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_242);
if (x_252 == 0)
{
return x_242;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_242, 0);
x_254 = lean_ctor_get(x_242, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_242);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_232);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_256 = l_Lean_Name_toString___closed__1;
x_257 = l_Lean_Name_toStringWithSep___main(x_256, x_2);
x_258 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_261 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
x_262 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_263 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = l_Lean_Meta_throwError___rarg(x_263, x_8, x_9, x_10, x_11, x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
return x_264;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_264);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_232);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_233);
if (x_275 == 0)
{
return x_233;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_233, 0);
x_277 = lean_ctor_get(x_233, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_233);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_229);
if (x_279 == 0)
{
return x_229;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_229, 0);
x_281 = lean_ctor_get(x_229, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_229);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
case 5:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_5, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_5, 1);
lean_inc(x_284);
lean_dec(x_5);
x_285 = lean_array_set(x_6, x_7, x_284);
x_286 = lean_unsigned_to_nat(1u);
x_287 = lean_nat_sub(x_7, x_286);
lean_dec(x_7);
x_5 = x_283;
x_6 = x_285;
x_7 = x_287;
goto _start;
}
case 6:
{
lean_object* x_289; 
lean_dec(x_7);
lean_inc(x_2);
x_289 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_unsigned_to_nat(0u);
x_292 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_291);
lean_inc(x_2);
x_293 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_290);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_330; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
x_296 = lean_ctor_get(x_293, 1);
lean_inc(x_296);
lean_dec(x_293);
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
lean_dec(x_294);
x_298 = lean_ctor_get(x_295, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
lean_dec(x_295);
x_330 = lean_unbox(x_299);
if (x_330 == 0)
{
lean_object* x_331; 
x_331 = lean_array_get_size(x_6);
x_300 = x_331;
goto block_329;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_array_get_size(x_6);
x_333 = lean_unsigned_to_nat(1u);
x_334 = lean_nat_sub(x_332, x_333);
lean_dec(x_332);
x_300 = x_334;
goto block_329;
}
block_329:
{
uint8_t x_301; 
x_301 = lean_nat_dec_lt(x_298, x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_302 = l_Lean_Meta_inferType(x_297, x_8, x_9, x_10, x_11, x_296);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = l_Lean_Expr_getAppNumArgsAux___main(x_303, x_291);
x_306 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_305);
x_307 = lean_mk_array(x_305, x_306);
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_nat_sub(x_305, x_308);
lean_dec(x_305);
x_310 = lean_unbox(x_299);
lean_dec(x_299);
x_311 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_292, x_298, x_310, x_300, x_303, x_307, x_309, x_8, x_9, x_10, x_11, x_304);
return x_311;
}
else
{
uint8_t x_312; 
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_292);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_302);
if (x_312 == 0)
{
return x_302;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_302, 0);
x_314 = lean_ctor_get(x_302, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_302);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_292);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_316 = l_Lean_Name_toString___closed__1;
x_317 = l_Lean_Name_toStringWithSep___main(x_316, x_2);
x_318 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_318, 0, x_317);
x_319 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_319, 0, x_318);
x_320 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_321 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_321, 0, x_320);
lean_ctor_set(x_321, 1, x_319);
x_322 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_323 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
x_324 = l_Lean_Meta_throwError___rarg(x_323, x_8, x_9, x_10, x_11, x_296);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_325 = !lean_is_exclusive(x_324);
if (x_325 == 0)
{
return x_324;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_324, 0);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_324);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_292);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_293);
if (x_335 == 0)
{
return x_293;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_293, 0);
x_337 = lean_ctor_get(x_293, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_293);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_289);
if (x_339 == 0)
{
return x_289;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_289, 0);
x_341 = lean_ctor_get(x_289, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_289);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
case 7:
{
lean_object* x_343; 
lean_dec(x_7);
lean_inc(x_2);
x_343 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_345 = lean_unsigned_to_nat(0u);
x_346 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_345);
lean_inc(x_2);
x_347 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_344);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_384; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_347, 1);
lean_inc(x_350);
lean_dec(x_347);
x_351 = lean_ctor_get(x_348, 0);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 1);
lean_inc(x_353);
lean_dec(x_349);
x_384 = lean_unbox(x_353);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_array_get_size(x_6);
x_354 = x_385;
goto block_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_array_get_size(x_6);
x_387 = lean_unsigned_to_nat(1u);
x_388 = lean_nat_sub(x_386, x_387);
lean_dec(x_386);
x_354 = x_388;
goto block_383;
}
block_383:
{
uint8_t x_355; 
x_355 = lean_nat_dec_lt(x_352, x_354);
if (x_355 == 0)
{
lean_object* x_356; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_356 = l_Lean_Meta_inferType(x_351, x_8, x_9, x_10, x_11, x_350);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Expr_getAppNumArgsAux___main(x_357, x_345);
x_360 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_359);
x_361 = lean_mk_array(x_359, x_360);
x_362 = lean_unsigned_to_nat(1u);
x_363 = lean_nat_sub(x_359, x_362);
lean_dec(x_359);
x_364 = lean_unbox(x_353);
lean_dec(x_353);
x_365 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_346, x_352, x_364, x_354, x_357, x_361, x_363, x_8, x_9, x_10, x_11, x_358);
return x_365;
}
else
{
uint8_t x_366; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_346);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_366 = !lean_is_exclusive(x_356);
if (x_366 == 0)
{
return x_356;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_356, 0);
x_368 = lean_ctor_get(x_356, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_356);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_346);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_370 = l_Lean_Name_toString___closed__1;
x_371 = l_Lean_Name_toStringWithSep___main(x_370, x_2);
x_372 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_372, 0, x_371);
x_373 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_375 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_377 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = l_Lean_Meta_throwError___rarg(x_377, x_8, x_9, x_10, x_11, x_350);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_379 = !lean_is_exclusive(x_378);
if (x_379 == 0)
{
return x_378;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_378, 0);
x_381 = lean_ctor_get(x_378, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_378);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_346);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_347);
if (x_389 == 0)
{
return x_347;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_347, 0);
x_391 = lean_ctor_get(x_347, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_347);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_343);
if (x_393 == 0)
{
return x_343;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_343, 0);
x_395 = lean_ctor_get(x_343, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_343);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
case 8:
{
lean_object* x_397; 
lean_dec(x_7);
lean_inc(x_2);
x_397 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_unsigned_to_nat(0u);
x_400 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_399);
lean_inc(x_2);
x_401 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_398);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_438; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_ctor_get(x_402, 0);
lean_inc(x_405);
lean_dec(x_402);
x_406 = lean_ctor_get(x_403, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_403, 1);
lean_inc(x_407);
lean_dec(x_403);
x_438 = lean_unbox(x_407);
if (x_438 == 0)
{
lean_object* x_439; 
x_439 = lean_array_get_size(x_6);
x_408 = x_439;
goto block_437;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_array_get_size(x_6);
x_441 = lean_unsigned_to_nat(1u);
x_442 = lean_nat_sub(x_440, x_441);
lean_dec(x_440);
x_408 = x_442;
goto block_437;
}
block_437:
{
uint8_t x_409; 
x_409 = lean_nat_dec_lt(x_406, x_408);
if (x_409 == 0)
{
lean_object* x_410; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_410 = l_Lean_Meta_inferType(x_405, x_8, x_9, x_10, x_11, x_404);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; uint8_t x_418; lean_object* x_419; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = l_Lean_Expr_getAppNumArgsAux___main(x_411, x_399);
x_414 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_413);
x_415 = lean_mk_array(x_413, x_414);
x_416 = lean_unsigned_to_nat(1u);
x_417 = lean_nat_sub(x_413, x_416);
lean_dec(x_413);
x_418 = lean_unbox(x_407);
lean_dec(x_407);
x_419 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_400, x_406, x_418, x_408, x_411, x_415, x_417, x_8, x_9, x_10, x_11, x_412);
return x_419;
}
else
{
uint8_t x_420; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_400);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_420 = !lean_is_exclusive(x_410);
if (x_420 == 0)
{
return x_410;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_410, 0);
x_422 = lean_ctor_get(x_410, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_410);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_400);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_424 = l_Lean_Name_toString___closed__1;
x_425 = l_Lean_Name_toStringWithSep___main(x_424, x_2);
x_426 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_426, 0, x_425);
x_427 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_427, 0, x_426);
x_428 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_429 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_427);
x_430 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_431 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
x_432 = l_Lean_Meta_throwError___rarg(x_431, x_8, x_9, x_10, x_11, x_404);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_433 = !lean_is_exclusive(x_432);
if (x_433 == 0)
{
return x_432;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_432, 0);
x_435 = lean_ctor_get(x_432, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_432);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
else
{
uint8_t x_443; 
lean_dec(x_400);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_443 = !lean_is_exclusive(x_401);
if (x_443 == 0)
{
return x_401;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_401, 0);
x_445 = lean_ctor_get(x_401, 1);
lean_inc(x_445);
lean_inc(x_444);
lean_dec(x_401);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
return x_446;
}
}
}
else
{
uint8_t x_447; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_447 = !lean_is_exclusive(x_397);
if (x_447 == 0)
{
return x_397;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_397, 0);
x_449 = lean_ctor_get(x_397, 1);
lean_inc(x_449);
lean_inc(x_448);
lean_dec(x_397);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
return x_450;
}
}
}
case 9:
{
lean_object* x_451; 
lean_dec(x_7);
lean_inc(x_2);
x_451 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = lean_unsigned_to_nat(0u);
x_454 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_453);
lean_inc(x_2);
x_455 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_452);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_492; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
x_458 = lean_ctor_get(x_455, 1);
lean_inc(x_458);
lean_dec(x_455);
x_459 = lean_ctor_get(x_456, 0);
lean_inc(x_459);
lean_dec(x_456);
x_460 = lean_ctor_get(x_457, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_457, 1);
lean_inc(x_461);
lean_dec(x_457);
x_492 = lean_unbox(x_461);
if (x_492 == 0)
{
lean_object* x_493; 
x_493 = lean_array_get_size(x_6);
x_462 = x_493;
goto block_491;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_array_get_size(x_6);
x_495 = lean_unsigned_to_nat(1u);
x_496 = lean_nat_sub(x_494, x_495);
lean_dec(x_494);
x_462 = x_496;
goto block_491;
}
block_491:
{
uint8_t x_463; 
x_463 = lean_nat_dec_lt(x_460, x_462);
if (x_463 == 0)
{
lean_object* x_464; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_464 = l_Lean_Meta_inferType(x_459, x_8, x_9, x_10, x_11, x_458);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec(x_464);
x_467 = l_Lean_Expr_getAppNumArgsAux___main(x_465, x_453);
x_468 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_467);
x_469 = lean_mk_array(x_467, x_468);
x_470 = lean_unsigned_to_nat(1u);
x_471 = lean_nat_sub(x_467, x_470);
lean_dec(x_467);
x_472 = lean_unbox(x_461);
lean_dec(x_461);
x_473 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_454, x_460, x_472, x_462, x_465, x_469, x_471, x_8, x_9, x_10, x_11, x_466);
return x_473;
}
else
{
uint8_t x_474; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_454);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_474 = !lean_is_exclusive(x_464);
if (x_474 == 0)
{
return x_464;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_464, 0);
x_476 = lean_ctor_get(x_464, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_464);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_454);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_478 = l_Lean_Name_toString___closed__1;
x_479 = l_Lean_Name_toStringWithSep___main(x_478, x_2);
x_480 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_480, 0, x_479);
x_481 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_482 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_483 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_481);
x_484 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_485 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
x_486 = l_Lean_Meta_throwError___rarg(x_485, x_8, x_9, x_10, x_11, x_458);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
return x_486;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_486, 0);
x_489 = lean_ctor_get(x_486, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_486);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
}
else
{
uint8_t x_497; 
lean_dec(x_454);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_497 = !lean_is_exclusive(x_455);
if (x_497 == 0)
{
return x_455;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_455, 0);
x_499 = lean_ctor_get(x_455, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_455);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_501 = !lean_is_exclusive(x_451);
if (x_501 == 0)
{
return x_451;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_451, 0);
x_503 = lean_ctor_get(x_451, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_451);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
case 10:
{
lean_object* x_505; 
lean_dec(x_7);
lean_inc(x_2);
x_505 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_507 = lean_unsigned_to_nat(0u);
x_508 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_507);
lean_inc(x_2);
x_509 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_506);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_546; 
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_510, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_509, 1);
lean_inc(x_512);
lean_dec(x_509);
x_513 = lean_ctor_get(x_510, 0);
lean_inc(x_513);
lean_dec(x_510);
x_514 = lean_ctor_get(x_511, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_511, 1);
lean_inc(x_515);
lean_dec(x_511);
x_546 = lean_unbox(x_515);
if (x_546 == 0)
{
lean_object* x_547; 
x_547 = lean_array_get_size(x_6);
x_516 = x_547;
goto block_545;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_array_get_size(x_6);
x_549 = lean_unsigned_to_nat(1u);
x_550 = lean_nat_sub(x_548, x_549);
lean_dec(x_548);
x_516 = x_550;
goto block_545;
}
block_545:
{
uint8_t x_517; 
x_517 = lean_nat_dec_lt(x_514, x_516);
if (x_517 == 0)
{
lean_object* x_518; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_518 = l_Lean_Meta_inferType(x_513, x_8, x_9, x_10, x_11, x_512);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = l_Lean_Expr_getAppNumArgsAux___main(x_519, x_507);
x_522 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_521);
x_523 = lean_mk_array(x_521, x_522);
x_524 = lean_unsigned_to_nat(1u);
x_525 = lean_nat_sub(x_521, x_524);
lean_dec(x_521);
x_526 = lean_unbox(x_515);
lean_dec(x_515);
x_527 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_508, x_514, x_526, x_516, x_519, x_523, x_525, x_8, x_9, x_10, x_11, x_520);
return x_527;
}
else
{
uint8_t x_528; 
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_508);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_518);
if (x_528 == 0)
{
return x_518;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_518, 0);
x_530 = lean_ctor_get(x_518, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_518);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_508);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_532 = l_Lean_Name_toString___closed__1;
x_533 = l_Lean_Name_toStringWithSep___main(x_532, x_2);
x_534 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_534, 0, x_533);
x_535 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_535, 0, x_534);
x_536 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_537 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_539 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_Lean_Meta_throwError___rarg(x_539, x_8, x_9, x_10, x_11, x_512);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_541 = !lean_is_exclusive(x_540);
if (x_541 == 0)
{
return x_540;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_540, 0);
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_540);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
return x_544;
}
}
}
}
else
{
uint8_t x_551; 
lean_dec(x_508);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_551 = !lean_is_exclusive(x_509);
if (x_551 == 0)
{
return x_509;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_509, 0);
x_553 = lean_ctor_get(x_509, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_509);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_555 = !lean_is_exclusive(x_505);
if (x_555 == 0)
{
return x_505;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_505, 0);
x_557 = lean_ctor_get(x_505, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_505);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
case 11:
{
lean_object* x_559; 
lean_dec(x_7);
lean_inc(x_2);
x_559 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
lean_dec(x_559);
x_561 = lean_unsigned_to_nat(0u);
x_562 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_561);
lean_inc(x_2);
x_563 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_560);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; uint8_t x_600; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
lean_dec(x_563);
x_567 = lean_ctor_get(x_564, 0);
lean_inc(x_567);
lean_dec(x_564);
x_568 = lean_ctor_get(x_565, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_565, 1);
lean_inc(x_569);
lean_dec(x_565);
x_600 = lean_unbox(x_569);
if (x_600 == 0)
{
lean_object* x_601; 
x_601 = lean_array_get_size(x_6);
x_570 = x_601;
goto block_599;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_array_get_size(x_6);
x_603 = lean_unsigned_to_nat(1u);
x_604 = lean_nat_sub(x_602, x_603);
lean_dec(x_602);
x_570 = x_604;
goto block_599;
}
block_599:
{
uint8_t x_571; 
x_571 = lean_nat_dec_lt(x_568, x_570);
if (x_571 == 0)
{
lean_object* x_572; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_572 = l_Lean_Meta_inferType(x_567, x_8, x_9, x_10, x_11, x_566);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = l_Lean_Expr_getAppNumArgsAux___main(x_573, x_561);
x_576 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_575);
x_577 = lean_mk_array(x_575, x_576);
x_578 = lean_unsigned_to_nat(1u);
x_579 = lean_nat_sub(x_575, x_578);
lean_dec(x_575);
x_580 = lean_unbox(x_569);
lean_dec(x_569);
x_581 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_562, x_568, x_580, x_570, x_573, x_577, x_579, x_8, x_9, x_10, x_11, x_574);
return x_581;
}
else
{
uint8_t x_582; 
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_562);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_572);
if (x_582 == 0)
{
return x_572;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_572, 0);
x_584 = lean_ctor_get(x_572, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_572);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_562);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_586 = l_Lean_Name_toString___closed__1;
x_587 = l_Lean_Name_toStringWithSep___main(x_586, x_2);
x_588 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_588, 0, x_587);
x_589 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_589, 0, x_588);
x_590 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_591 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_593 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
x_594 = l_Lean_Meta_throwError___rarg(x_593, x_8, x_9, x_10, x_11, x_566);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_595 = !lean_is_exclusive(x_594);
if (x_595 == 0)
{
return x_594;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_594, 0);
x_597 = lean_ctor_get(x_594, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_594);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_562);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_563);
if (x_605 == 0)
{
return x_563;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_563, 0);
x_607 = lean_ctor_get(x_563, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_563);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
else
{
uint8_t x_609; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_609 = !lean_is_exclusive(x_559);
if (x_609 == 0)
{
return x_559;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_559, 0);
x_611 = lean_ctor_get(x_559, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_559);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
default: 
{
lean_object* x_613; 
lean_dec(x_7);
lean_inc(x_2);
x_613 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_613) == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_unsigned_to_nat(0u);
x_616 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_615);
lean_inc(x_2);
x_617 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_614);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_654; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
x_620 = lean_ctor_get(x_617, 1);
lean_inc(x_620);
lean_dec(x_617);
x_621 = lean_ctor_get(x_618, 0);
lean_inc(x_621);
lean_dec(x_618);
x_622 = lean_ctor_get(x_619, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_619, 1);
lean_inc(x_623);
lean_dec(x_619);
x_654 = lean_unbox(x_623);
if (x_654 == 0)
{
lean_object* x_655; 
x_655 = lean_array_get_size(x_6);
x_624 = x_655;
goto block_653;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_array_get_size(x_6);
x_657 = lean_unsigned_to_nat(1u);
x_658 = lean_nat_sub(x_656, x_657);
lean_dec(x_656);
x_624 = x_658;
goto block_653;
}
block_653:
{
uint8_t x_625; 
x_625 = lean_nat_dec_lt(x_622, x_624);
if (x_625 == 0)
{
lean_object* x_626; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_626 = l_Lean_Meta_inferType(x_621, x_8, x_9, x_10, x_11, x_620);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; uint8_t x_634; lean_object* x_635; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_626, 1);
lean_inc(x_628);
lean_dec(x_626);
x_629 = l_Lean_Expr_getAppNumArgsAux___main(x_627, x_615);
x_630 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_629);
x_631 = lean_mk_array(x_629, x_630);
x_632 = lean_unsigned_to_nat(1u);
x_633 = lean_nat_sub(x_629, x_632);
lean_dec(x_629);
x_634 = lean_unbox(x_623);
lean_dec(x_623);
x_635 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_616, x_622, x_634, x_624, x_627, x_631, x_633, x_8, x_9, x_10, x_11, x_628);
return x_635;
}
else
{
uint8_t x_636; 
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_616);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_636 = !lean_is_exclusive(x_626);
if (x_636 == 0)
{
return x_626;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_626, 0);
x_638 = lean_ctor_get(x_626, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_626);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_616);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_640 = l_Lean_Name_toString___closed__1;
x_641 = l_Lean_Name_toStringWithSep___main(x_640, x_2);
x_642 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_643 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_643, 0, x_642);
x_644 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_645 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_643);
x_646 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_647 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
x_648 = l_Lean_Meta_throwError___rarg(x_647, x_8, x_9, x_10, x_11, x_620);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_649 = !lean_is_exclusive(x_648);
if (x_649 == 0)
{
return x_648;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_648, 0);
x_651 = lean_ctor_get(x_648, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_648);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
}
else
{
uint8_t x_659; 
lean_dec(x_616);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_659 = !lean_is_exclusive(x_617);
if (x_659 == 0)
{
return x_617;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; 
x_660 = lean_ctor_get(x_617, 0);
x_661 = lean_ctor_get(x_617, 1);
lean_inc(x_661);
lean_inc(x_660);
lean_dec(x_617);
x_662 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_662, 0, x_660);
lean_ctor_set(x_662, 1, x_661);
return x_662;
}
}
}
else
{
uint8_t x_663; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_663 = !lean_is_exclusive(x_613);
if (x_663 == 0)
{
return x_613;
}
else
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_664 = lean_ctor_get(x_613, 0);
x_665 = lean_ctor_get(x_613, 1);
lean_inc(x_665);
lean_inc(x_664);
lean_dec(x_613);
x_666 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_666, 0, x_664);
lean_ctor_set(x_666, 1, x_665);
return x_666;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_17 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_ConstantInfo_type(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed), 10, 3);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_10);
x_14 = l_Lean_Meta_forallTelescopeReducing___rarg(x_12, x_13, x_3, x_4, x_5, x_6, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_8);
lean_dec(x_8);
x_19 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
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
x_8 = l_Lean_Meta_getConstInfo(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Lean_Core_throwError___rarg(x_7, x_2, x_3, x_4);
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
lean_object* _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1() {
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
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
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
x_42 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
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
x_18 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
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
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_19, x_17, x_2, x_2);
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
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_29, x_28, x_2, x_2);
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
x_37 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_33, x_31, x_2, x_2);
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
x_40 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_3, x_39, x_38, x_2, x_2);
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
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_15);
lean_dec(x_15);
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_take(x_13, x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_io_ref_set(x_13, x_24, x_22);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_19);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
return x_3;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
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
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(x_18, x_7);
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
x_23 = lean_io_ref_take(x_3, x_21);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_io_ref_set(x_3, x_27, x_25);
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
x_38 = l_Lean_Name_toString___closed__1;
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
x_58 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(x_57, x_46);
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
x_62 = lean_io_ref_take(x_3, x_60);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_61);
x_65 = x_61;
x_66 = lean_array_push(x_63, x_65);
x_67 = lean_io_ref_set(x_3, x_66, x_64);
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
x_76 = l_Lean_Name_toString___closed__1;
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
x_7 = l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(x_6, x_3, x_4, x_5);
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
x_7 = l_Lean_Meta_MetaM_run_x27___rarg___closed__3;
x_8 = lean_io_mk_ref(x_7, x_5);
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
x_14 = lean_io_ref_get(x_9, x_13);
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
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(x_1, x_2, x_3, x_4);
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
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(x_1, x_2, x_3, x_4, x_5);
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
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
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
x_7 = l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_6, x_3);
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
x_16 = l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(x_10, x_12, x_11, x_15);
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
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(x_1, x_2, x_3, x_4);
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
x_8 = l_Lean_Meta_getConstInfo(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_9, 0);
lean_inc(x_19);
lean_dec(x_9);
x_20 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_19, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_11 = x_21;
goto block_18;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_9, x_2, x_3, x_4, x_5, x_6, x_10);
return x_22;
}
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_12 = l_Lean_Core_getEnv___rarg(x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_recursorAttribute;
x_16 = l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(x_15, x_13, x_1);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_9, x_16, x_3, x_4, x_5, x_6, x_14);
return x_17;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
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
if (_G_initialized) return lean_mk_io_result(lean_box(0));
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
l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1);
l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2);
l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3);
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
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__2);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__2);
l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3 = _init_l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__2);
l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2);
l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3);
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
l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1 = _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1);
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
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
