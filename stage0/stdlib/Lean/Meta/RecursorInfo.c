// Lean compiler output
// Module: Lean.Meta.RecursorInfo
// Imports: Init Lean.AuxRecursor Lean.Util.FindExpr Lean.Meta.ExprDefEq Lean.Meta.Message
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
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4;
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__5(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object**);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__4;
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(lean_object*);
lean_object* l_Lean_Core_getEnv___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13;
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__14;
lean_object* l_Lean_Meta_recOnSuffix;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__5;
lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__5;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
lean_object* l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* lean_io_ref_take(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
lean_object* l_Lean_Core_setEnv(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__8;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__4;
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
extern lean_object* l_IO_FS_Handle_putStrLn___rarg___closed__1;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix;
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1;
extern lean_object* l_Lean_Meta_run___rarg___closed__5;
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__13;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__7;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__1;
lean_object* l_Lean_Meta_throwOther___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7___boxed(lean_object*);
lean_object* l_Array_back___at___private_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(lean_object*);
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
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__4;
lean_object* l_Lean_Meta_getMajorPos_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___closed__1;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
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
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__3;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__12;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__16;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__4;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_ofExcept___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MetavarContext_Inhabited___closed__1;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__10;
extern lean_object* l_Lean_Meta_run___rarg___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__2___lambda__1(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__15;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__3;
extern lean_object* l_Lean_defaultMaxRecDepth;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2;
lean_object* l_Lean_Meta_recOnSuffix___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameGenerator_Inhabited___closed__3;
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
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_RecursorVal_getInduct(x_2);
lean_inc(x_5);
x_6 = l_Lean_Meta_getConstInfo(x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 5)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_List_lengthAux___main___rarg(x_12, x_13);
lean_dec(x_12);
lean_inc(x_14);
x_15 = l_List_range(x_14);
x_16 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_15);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_List_lengthAux___main___rarg(x_18, x_13);
lean_dec(x_18);
x_20 = lean_nat_dec_eq(x_19, x_14);
lean_dec(x_14);
lean_dec(x_19);
x_21 = lean_ctor_get(x_2, 5);
lean_inc(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_inc(x_21);
x_24 = l_List_replicate___rarg(x_21, x_23);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_inc(x_25);
x_26 = l_List_range(x_25);
x_27 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_26);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_28);
x_29 = l_List_range(x_28);
x_30 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_25, x_29);
x_31 = lean_nat_add(x_28, x_25);
lean_dec(x_25);
lean_dec(x_28);
x_32 = lean_nat_add(x_31, x_21);
lean_dec(x_21);
lean_dec(x_31);
x_33 = lean_ctor_get(x_2, 4);
lean_inc(x_33);
x_34 = lean_nat_add(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_34, x_35);
lean_dec(x_34);
x_37 = lean_ctor_get_uint8(x_10, sizeof(void*)*5);
lean_dec(x_10);
x_38 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_20 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_16);
x_41 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_36);
lean_ctor_set(x_41, 4, x_38);
lean_ctor_set(x_41, 5, x_27);
lean_ctor_set(x_41, 6, x_30);
lean_ctor_set(x_41, 7, x_24);
lean_ctor_set_uint8(x_41, sizeof(void*)*8, x_22);
lean_ctor_set_uint8(x_41, sizeof(void*)*8 + 1, x_37);
lean_ctor_set(x_6, 0, x_41);
return x_6;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_5);
lean_ctor_set(x_42, 2, x_16);
lean_ctor_set(x_42, 3, x_36);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set(x_42, 5, x_27);
lean_ctor_set(x_42, 6, x_30);
lean_ctor_set(x_42, 7, x_24);
lean_ctor_set_uint8(x_42, sizeof(void*)*8, x_22);
lean_ctor_set_uint8(x_42, sizeof(void*)*8 + 1, x_37);
lean_ctor_set(x_6, 0, x_42);
return x_6;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_43 = lean_ctor_get(x_6, 1);
lean_inc(x_43);
lean_dec(x_6);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_List_lengthAux___main___rarg(x_46, x_47);
lean_dec(x_46);
lean_inc(x_48);
x_49 = l_List_range(x_48);
x_50 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_49);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_List_lengthAux___main___rarg(x_52, x_47);
lean_dec(x_52);
x_54 = lean_nat_dec_eq(x_53, x_48);
lean_dec(x_48);
lean_dec(x_53);
x_55 = lean_ctor_get(x_2, 5);
lean_inc(x_55);
x_56 = 1;
x_57 = lean_box(x_56);
lean_inc(x_55);
x_58 = l_List_replicate___rarg(x_55, x_57);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_inc(x_59);
x_60 = l_List_range(x_59);
x_61 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_60);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_inc(x_62);
x_63 = l_List_range(x_62);
x_64 = l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_59, x_63);
x_65 = lean_nat_add(x_62, x_59);
lean_dec(x_59);
lean_dec(x_62);
x_66 = lean_nat_add(x_65, x_55);
lean_dec(x_55);
lean_dec(x_65);
x_67 = lean_ctor_get(x_2, 4);
lean_inc(x_67);
x_68 = lean_nat_add(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_68, x_69);
lean_dec(x_68);
x_71 = lean_ctor_get_uint8(x_44, sizeof(void*)*5);
lean_dec(x_44);
x_72 = l_Lean_RecursorVal_getMajorIdx(x_2);
lean_dec(x_2);
if (x_54 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_50);
x_75 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_5);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_70);
lean_ctor_set(x_75, 4, x_72);
lean_ctor_set(x_75, 5, x_61);
lean_ctor_set(x_75, 6, x_64);
lean_ctor_set(x_75, 7, x_58);
lean_ctor_set_uint8(x_75, sizeof(void*)*8, x_56);
lean_ctor_set_uint8(x_75, sizeof(void*)*8 + 1, x_71);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_43);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_5);
lean_ctor_set(x_77, 2, x_50);
lean_ctor_set(x_77, 3, x_70);
lean_ctor_set(x_77, 4, x_72);
lean_ctor_set(x_77, 5, x_61);
lean_ctor_set(x_77, 6, x_64);
lean_ctor_set(x_77, 7, x_58);
lean_ctor_set_uint8(x_77, sizeof(void*)*8, x_56);
lean_ctor_set_uint8(x_77, sizeof(void*)*8 + 1, x_71);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_43);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_6, 1);
lean_inc(x_79);
lean_dec(x_6);
x_80 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
x_81 = lean_box(0);
x_82 = l_Lean_Meta_throwOther___rarg(x_80, x_81, x_3, x_79);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_6);
if (x_83 == 0)
{
return x_6;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_6, 0);
x_85 = lean_ctor_get(x_6, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_6);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
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
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_auxRecExt;
x_7 = l_Lean_TagDeclarationExtension_isTagged(x_6, x_5, x_1);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_55; uint8_t x_56; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_55 = l_Lean_Meta_recOnSuffix;
x_56 = lean_string_dec_eq(x_11, x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Meta_casesOnSuffix;
x_58 = lean_string_dec_eq(x_11, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Meta_brecOnSuffix;
x_60 = lean_string_dec_eq(x_11, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_11);
lean_dec(x_10);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_4);
return x_62;
}
else
{
lean_object* x_63; 
x_63 = lean_box(0);
x_12 = x_63;
goto block_54;
}
}
else
{
lean_object* x_64; 
x_64 = lean_box(0);
x_12 = x_64;
goto block_54;
}
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_12 = x_65;
goto block_54;
}
block_54:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_13 = l_Lean_mkRecFor___closed__1;
x_14 = lean_name_mk_string(x_10, x_13);
x_15 = l_Lean_Meta_getConstInfo(x_14, x_3, x_4);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 7)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 3);
lean_inc(x_21);
x_22 = lean_nat_add(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_23 = l_Lean_Meta_casesOnSuffix;
x_24 = lean_string_dec_eq(x_11, x_23);
lean_dec(x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 4);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_nat_add(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_15, 0, x_27);
return x_15;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_22, x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_15, 0, x_30);
return x_15;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 3);
lean_inc(x_34);
x_35 = lean_nat_add(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = l_Lean_Meta_casesOnSuffix;
x_37 = lean_string_dec_eq(x_11, x_36);
lean_dec(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_32, 4);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_nat_add(x_35, x_38);
lean_dec(x_38);
lean_dec(x_35);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_32);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_35, x_42);
lean_dec(x_35);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_16);
lean_dec(x_11);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_dec(x_15);
x_47 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
x_48 = lean_box(0);
x_49 = l_Lean_Meta_throwOther___rarg(x_47, x_48, x_3, x_46);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
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
lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_4);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_1);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_4);
return x_68;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
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
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isFVar(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_1);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_throwOther___rarg(x_16, x_17, x_4, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_get_size(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_3, x_3, x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_1);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__6;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwOther___rarg(x_33, x_34, x_4, x_5);
return x_35;
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
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
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
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_back___at___private_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_9, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Core_getConstInfo___closed__5;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwOther___rarg(x_19, x_20, x_6, x_7);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_1);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Meta_throwOther___rarg(x_39, x_40, x_6, x_7);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
return x_41;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_1);
x_46 = lean_ctor_get(x_2, 0);
x_47 = lean_array_get_size(x_3);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = l_Nat_repr(x_47);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_throwOther___rarg(x_55, x_56, x_6, x_7);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_47);
x_58 = lean_array_fget(x_3, x_46);
x_59 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_5, x_58);
x_60 = lean_box(x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_7);
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
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Meta_isExprDefEq(x_10, x_1, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_nat_sub(x_4, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = l_Lean_Expr_Inhabited;
x_16 = lean_array_get(x_15, x_2, x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_16);
x_17 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_16, x_3, x_9, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_fvarId_x21(x_16);
lean_dec(x_16);
lean_inc(x_7);
x_21 = l_Lean_Meta_getLocalDecl(x_20, x_7, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_binderInfo(x_22);
lean_dec(x_22);
x_25 = l_Lean_BinderInfo_isInstImplicit(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_6);
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
x_32 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = l_Lean_Meta_throwOther___rarg(x_33, x_34, x_7, x_23);
lean_dec(x_7);
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
lean_object* x_40; 
x_40 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_40;
x_8 = x_23;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_16);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_47;
x_8 = x_46;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_6);
lean_ctor_set(x_53, 1, x_8);
return x_53;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_empty___closed__1;
lean_inc(x_3);
x_8 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_4, x_3, x_3, x_7, x_5, x_6);
lean_dec(x_3);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
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
x_14 = l_Array_toList___rarg(x_12);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_fget(x_2, x_3);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Meta_isExprDefEq(x_10, x_1, x_4, x_5);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_3 = x_16;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_11, 0, x_20);
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_nat_sub(x_3, x_4);
x_18 = lean_nat_add(x_17, x_16);
lean_dec(x_16);
lean_dec(x_17);
x_19 = l_Lean_Expr_Inhabited;
x_20 = lean_array_get(x_19, x_2, x_18);
lean_dec(x_18);
lean_inc(x_9);
x_21 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_20, x_5, x_11, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_8);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Name_toString___closed__1;
x_25 = l_Lean_Name_toStringWithSep___main(x_24, x_1);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
x_31 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Meta_throwOther___rarg(x_31, x_32, x_9, x_23);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_dec(x_21);
x_39 = lean_ctor_get(x_22, 0);
lean_inc(x_39);
lean_dec(x_22);
x_40 = lean_array_push(x_8, x_39);
x_7 = x_14;
x_8 = x_40;
x_10 = x_38;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
return x_21;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get(x_21, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_21);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_10);
return x_46;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Array_empty___closed__1;
lean_inc(x_4);
x_9 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_4, x_4, x_8, x_6, x_7);
lean_dec(x_4);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Array_toList___rarg(x_11);
lean_dec(x_11);
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
x_15 = l_Array_toList___rarg(x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
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
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
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
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_18; 
lean_dec(x_1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
return x_18;
}
case 4:
{
lean_object* x_19; 
lean_dec(x_1);
lean_inc(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
default: 
{
lean_object* x_20; 
x_20 = lean_box(0);
x_5 = x_20;
goto block_16;
}
}
}
else
{
lean_object* x_21; 
x_21 = lean_box(0);
x_5 = x_21;
goto block_16;
}
block_16:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Meta_throwOther___rarg(x_13, x_14, x_3, x_4);
return x_15;
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
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
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_9);
x_11 = l_Lean_mkLevelParam(x_9);
x_12 = lean_level_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_11, x_3, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__3;
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Name_toStringWithSep___main(x_15, x_9);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Core_getConstInfo___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwOther___rarg(x_28, x_29, x_6, x_7);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
x_35 = lean_ctor_get(x_14, 0);
lean_inc(x_35);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_array_push(x_4, x_36);
x_4 = x_37;
x_5 = x_10;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_11);
lean_dec(x_9);
x_39 = lean_box(0);
x_40 = lean_array_push(x_4, x_39);
x_4 = x_40;
x_5 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_List_redLength___main___rarg(x_4);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___main___rarg(x_4, x_8);
x_10 = l_Array_empty___closed__1;
x_11 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_3, x_9, x_10, x_2, x_5, x_6);
lean_dec(x_9);
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
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_5);
lean_inc(x_6);
x_13 = l_Lean_Meta_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = 8192;
x_18 = l_Lean_Expr_FindImpl_initCache;
x_19 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_17, x_15, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_13, 0, x_25);
return x_13;
}
}
else
{
lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = 8192;
x_29 = l_Lean_Expr_FindImpl_initCache;
x_30 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_28, x_26, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_5 = x_33;
x_7 = x_27;
goto _start;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
x_35 = 1;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_6);
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_array_set(x_6, x_7, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_5 = x_10;
x_6 = x_12;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_expr_eqv(x_5, x_1);
lean_dec(x_5);
x_17 = lean_box(x_16);
x_18 = lean_array_push(x_2, x_17);
if (x_3 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_array_get_size(x_4);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_4, x_4, x_19, x_20, x_8, x_9);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
x_33 = lean_box(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_9);
return x_35;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_8);
x_10 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
x_14 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_13, x_6, x_7);
return x_14;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_7, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_39; uint8_t x_40; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_7, x_13);
lean_dec(x_7);
x_15 = lean_nat_sub(x_6, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_39 = lean_nat_add(x_2, x_13);
x_40 = lean_nat_dec_lt(x_16, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_nat_sub(x_4, x_3);
x_42 = lean_nat_dec_le(x_41, x_16);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_17 = x_43;
goto block_38;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_16, x_4);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_17 = x_45;
goto block_38;
}
else
{
lean_dec(x_16);
x_7 = x_14;
goto _start;
}
}
}
else
{
lean_dec(x_16);
x_7 = x_14;
goto _start;
}
block_38:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_1, x_16);
lean_dec(x_16);
lean_inc(x_9);
x_22 = l_Lean_Meta_inferType(x_21, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
x_25 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed), 7, 3);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_18);
lean_closure_set(x_25, 2, x_19);
lean_inc(x_9);
x_26 = l_Lean_Meta_forallTelescopeReducing___rarg(x_23, x_25, x_9, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_7 = x_14;
x_8 = x_27;
x_10 = x_28;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
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
}
else
{
lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_10);
return x_48;
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
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_8);
x_10 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_8, x_8, x_9, x_6, x_7);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_10;
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
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = l_Array_toList___rarg(x_22);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_object* l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_anyRangeMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isSort(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_throwOther___rarg(x_19, x_20, x_5, x_6);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_get_size(x_2);
x_23 = lean_array_get_size(x_4);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_25 = l_Lean_Name_toString___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_1);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_box(0);
x_38 = l_Lean_Meta_throwOther___rarg(x_36, x_37, x_5, x_6);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_1);
x_18 = l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_15, x_14, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_20 = l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_15, x_16, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_ConstantInfo_lparams(x_3);
lean_inc(x_1);
x_24 = l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_23, x_21, x_4, x_16, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_5, x_6, x_7, x_8, x_9, x_16, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_get_size(x_5);
x_33 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_10);
lean_ctor_set(x_33, 2, x_25);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_8);
lean_ctor_set(x_33, 5, x_12);
lean_ctor_set(x_33, 6, x_13);
lean_ctor_set(x_33, 7, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*8, x_11);
x_34 = lean_unbox(x_31);
lean_dec(x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*8 + 1, x_34);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_array_get_size(x_5);
x_40 = lean_alloc_ctor(0, 8, 2);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_25);
lean_ctor_set(x_40, 3, x_39);
lean_ctor_set(x_40, 4, x_8);
lean_ctor_set(x_40, 5, x_12);
lean_ctor_set(x_40, 6, x_13);
lean_ctor_set(x_40, 7, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_11);
x_41 = lean_unbox(x_38);
lean_dec(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*8 + 1, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
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
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
return x_24;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_24, 0);
x_49 = lean_ctor_get(x_24, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_24);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
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
uint8_t x_55; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
return x_18;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = lean_ctor_get(x_18, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_18);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (lean_obj_tag(x_10)) {
case 4:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
lean_inc(x_13);
lean_inc(x_6);
lean_inc(x_2);
x_17 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_3, x_6, x_11, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_9);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_11, x_13, x_19);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_4);
x_23 = l_Lean_Meta_inferType(x_4, x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(x_8);
x_27 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 17, 13);
lean_closure_set(x_27, 0, x_2);
lean_closure_set(x_27, 1, x_5);
lean_closure_set(x_27, 2, x_1);
lean_closure_set(x_27, 3, x_16);
lean_closure_set(x_27, 4, x_3);
lean_closure_set(x_27, 5, x_6);
lean_closure_set(x_27, 6, x_9);
lean_closure_set(x_27, 7, x_7);
lean_closure_set(x_27, 8, x_4);
lean_closure_set(x_27, 9, x_15);
lean_closure_set(x_27, 10, x_26);
lean_closure_set(x_27, 11, x_18);
lean_closure_set(x_27, 12, x_21);
x_28 = l_Lean_Meta_forallTelescopeReducing___rarg(x_24, x_27, x_13, x_25);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
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
lean_dec(x_16);
lean_dec(x_15);
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
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
case 5:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_10, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_dec(x_10);
x_43 = lean_array_set(x_11, x_12, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_12, x_44);
lean_dec(x_12);
x_10 = x_41;
x_11 = x_43;
x_12 = x_45;
goto _start;
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
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
x_47 = l_Lean_Name_toString___closed__1;
x_48 = l_Lean_Name_toStringWithSep___main(x_47, x_2);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_box(0);
x_56 = l_Lean_Meta_throwOther___rarg(x_54, x_55, x_13, x_14);
lean_dec(x_13);
return x_56;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
switch (lean_obj_tag(x_11)) {
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_10);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
lean_inc(x_14);
lean_inc(x_6);
lean_inc(x_2);
x_18 = l___private_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_3, x_6, x_12, x_14, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_2);
x_21 = l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_12, x_14, x_20);
lean_dec(x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_4);
x_24 = l_Lean_Meta_inferType(x_4, x_14, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(x_8);
x_28 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 17, 13);
lean_closure_set(x_28, 0, x_2);
lean_closure_set(x_28, 1, x_5);
lean_closure_set(x_28, 2, x_1);
lean_closure_set(x_28, 3, x_17);
lean_closure_set(x_28, 4, x_3);
lean_closure_set(x_28, 5, x_6);
lean_closure_set(x_28, 6, x_9);
lean_closure_set(x_28, 7, x_7);
lean_closure_set(x_28, 8, x_4);
lean_closure_set(x_28, 9, x_16);
lean_closure_set(x_28, 10, x_27);
lean_closure_set(x_28, 11, x_19);
lean_closure_set(x_28, 12, x_22);
x_29 = l_Lean_Meta_forallTelescopeReducing___rarg(x_25, x_28, x_14, x_26);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_17);
lean_dec(x_16);
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
case 5:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_11, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_array_set(x_12, x_13, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_13, x_45);
lean_dec(x_13);
x_11 = x_42;
x_12 = x_44;
x_13 = x_46;
goto _start;
}
default: 
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
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
x_48 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_10);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Meta_throwOther___rarg(x_49, x_50, x_14, x_15);
lean_dec(x_14);
return x_51;
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_2);
x_10 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_12);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_52; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_52 = lean_unbox(x_20);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_array_get_size(x_6);
x_21 = x_53;
goto block_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_array_get_size(x_6);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_54, x_55);
lean_dec(x_54);
x_21 = x_56;
goto block_51;
}
block_51:
{
uint8_t x_22; 
x_22 = lean_nat_dec_lt(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_8);
x_23 = l_Lean_Meta_inferType(x_18, x_8, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_24, x_12);
x_27 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_26);
x_28 = lean_mk_array(x_26, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_26, x_29);
lean_dec(x_26);
x_31 = lean_unbox(x_20);
lean_dec(x_20);
x_32 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_13, x_19, x_31, x_21, x_24, x_28, x_30, x_8, x_25);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = l_Lean_Name_toString___closed__1;
x_38 = l_Lean_Name_toStringWithSep___main(x_37, x_2);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Meta_throwOther___rarg(x_44, x_45, x_8, x_17);
lean_dec(x_8);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
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
return x_50;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_14);
if (x_57 == 0)
{
return x_14;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_14, 0);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_14);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_10);
if (x_61 == 0)
{
return x_10;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_10, 0);
x_63 = lean_ctor_get(x_10, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
case 1:
{
lean_object* x_65; 
lean_dec(x_7);
lean_inc(x_2);
x_65 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_67);
lean_inc(x_2);
x_69 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_107; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_ctor_get(x_71, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_107 = lean_unbox(x_75);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_array_get_size(x_6);
x_76 = x_108;
goto block_106;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_array_get_size(x_6);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_sub(x_109, x_110);
lean_dec(x_109);
x_76 = x_111;
goto block_106;
}
block_106:
{
uint8_t x_77; 
x_77 = lean_nat_dec_lt(x_74, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc(x_8);
x_78 = l_Lean_Meta_inferType(x_73, x_8, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Expr_getAppNumArgsAux___main(x_79, x_67);
x_82 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_81);
x_83 = lean_mk_array(x_81, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_81, x_84);
lean_dec(x_81);
x_86 = lean_unbox(x_75);
lean_dec(x_75);
x_87 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_68, x_74, x_86, x_76, x_79, x_83, x_85, x_8, x_80);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_68);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_78);
if (x_88 == 0)
{
return x_78;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_78, 0);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_78);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_68);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = l_Lean_Name_toString___closed__1;
x_93 = l_Lean_Name_toStringWithSep___main(x_92, x_2);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_99 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_box(0);
x_101 = l_Lean_Meta_throwOther___rarg(x_99, x_100, x_8, x_72);
lean_dec(x_8);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
return x_101;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_101, 0);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_68);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_69);
if (x_112 == 0)
{
return x_69;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_69, 0);
x_114 = lean_ctor_get(x_69, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_69);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_65);
if (x_116 == 0)
{
return x_65;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_65, 0);
x_118 = lean_ctor_get(x_65, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_65);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
case 2:
{
lean_object* x_120; 
lean_dec(x_7);
lean_inc(x_2);
x_120 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_unsigned_to_nat(0u);
x_123 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_122);
lean_inc(x_2);
x_124 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_162; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
lean_dec(x_126);
x_162 = lean_unbox(x_130);
if (x_162 == 0)
{
lean_object* x_163; 
x_163 = lean_array_get_size(x_6);
x_131 = x_163;
goto block_161;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_array_get_size(x_6);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_sub(x_164, x_165);
lean_dec(x_164);
x_131 = x_166;
goto block_161;
}
block_161:
{
uint8_t x_132; 
x_132 = lean_nat_dec_lt(x_129, x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_inc(x_8);
x_133 = l_Lean_Meta_inferType(x_128, x_8, x_127);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Expr_getAppNumArgsAux___main(x_134, x_122);
x_137 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_136);
x_138 = lean_mk_array(x_136, x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_sub(x_136, x_139);
lean_dec(x_136);
x_141 = lean_unbox(x_130);
lean_dec(x_130);
x_142 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_123, x_129, x_141, x_131, x_134, x_138, x_140, x_8, x_135);
return x_142;
}
else
{
uint8_t x_143; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_133);
if (x_143 == 0)
{
return x_133;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_133, 0);
x_145 = lean_ctor_get(x_133, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_133);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_123);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_147 = l_Lean_Name_toString___closed__1;
x_148 = l_Lean_Name_toStringWithSep___main(x_147, x_2);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_152 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_box(0);
x_156 = l_Lean_Meta_throwOther___rarg(x_154, x_155, x_8, x_127);
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
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_124);
if (x_167 == 0)
{
return x_124;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_124, 0);
x_169 = lean_ctor_get(x_124, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_124);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_120);
if (x_171 == 0)
{
return x_120;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_120, 0);
x_173 = lean_ctor_get(x_120, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_120);
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
x_175 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_177);
lean_inc(x_2);
x_179 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_217; 
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
x_217 = lean_unbox(x_185);
if (x_217 == 0)
{
lean_object* x_218; 
x_218 = lean_array_get_size(x_6);
x_186 = x_218;
goto block_216;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_array_get_size(x_6);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_sub(x_219, x_220);
lean_dec(x_219);
x_186 = x_221;
goto block_216;
}
block_216:
{
uint8_t x_187; 
x_187 = lean_nat_dec_lt(x_184, x_186);
if (x_187 == 0)
{
lean_object* x_188; 
lean_inc(x_8);
x_188 = l_Lean_Meta_inferType(x_183, x_8, x_182);
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
x_197 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_178, x_184, x_196, x_186, x_189, x_193, x_195, x_8, x_190);
return x_197;
}
else
{
uint8_t x_198; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_178);
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
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
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
x_210 = lean_box(0);
x_211 = l_Lean_Meta_throwOther___rarg(x_209, x_210, x_8, x_182);
lean_dec(x_8);
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
lean_dec(x_178);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_222 = !lean_is_exclusive(x_179);
if (x_222 == 0)
{
return x_179;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_179, 0);
x_224 = lean_ctor_get(x_179, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_179);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_175);
if (x_226 == 0)
{
return x_175;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_175, 0);
x_228 = lean_ctor_get(x_175, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_175);
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
lean_dec(x_7);
lean_inc(x_2);
x_230 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = lean_unsigned_to_nat(0u);
x_233 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_232);
lean_inc(x_2);
x_234 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_231);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_272; 
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
x_272 = lean_unbox(x_240);
if (x_272 == 0)
{
lean_object* x_273; 
x_273 = lean_array_get_size(x_6);
x_241 = x_273;
goto block_271;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_array_get_size(x_6);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_nat_sub(x_274, x_275);
lean_dec(x_274);
x_241 = x_276;
goto block_271;
}
block_271:
{
uint8_t x_242; 
x_242 = lean_nat_dec_lt(x_239, x_241);
if (x_242 == 0)
{
lean_object* x_243; 
lean_inc(x_8);
x_243 = l_Lean_Meta_inferType(x_238, x_8, x_237);
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
x_252 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_233, x_239, x_251, x_241, x_244, x_248, x_250, x_8, x_245);
return x_252;
}
else
{
uint8_t x_253; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_233);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_238);
lean_dec(x_233);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_257 = l_Lean_Name_toString___closed__1;
x_258 = l_Lean_Name_toStringWithSep___main(x_257, x_2);
x_259 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_262 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_264 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_box(0);
x_266 = l_Lean_Meta_throwOther___rarg(x_264, x_265, x_8, x_237);
lean_dec(x_8);
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
return x_266;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_266, 0);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_266);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_233);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_234);
if (x_277 == 0)
{
return x_234;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_234, 0);
x_279 = lean_ctor_get(x_234, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_234);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_230);
if (x_281 == 0)
{
return x_230;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_230, 0);
x_283 = lean_ctor_get(x_230, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_230);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
case 5:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_5, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_5, 1);
lean_inc(x_286);
lean_dec(x_5);
x_287 = lean_array_set(x_6, x_7, x_286);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_nat_sub(x_7, x_288);
lean_dec(x_7);
x_5 = x_285;
x_6 = x_287;
x_7 = x_289;
goto _start;
}
case 6:
{
lean_object* x_291; 
lean_dec(x_7);
lean_inc(x_2);
x_291 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_293 = lean_unsigned_to_nat(0u);
x_294 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_293);
lean_inc(x_2);
x_295 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_292);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_333; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_299 = lean_ctor_get(x_296, 0);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_ctor_get(x_297, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 1);
lean_inc(x_301);
lean_dec(x_297);
x_333 = lean_unbox(x_301);
if (x_333 == 0)
{
lean_object* x_334; 
x_334 = lean_array_get_size(x_6);
x_302 = x_334;
goto block_332;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_array_get_size(x_6);
x_336 = lean_unsigned_to_nat(1u);
x_337 = lean_nat_sub(x_335, x_336);
lean_dec(x_335);
x_302 = x_337;
goto block_332;
}
block_332:
{
uint8_t x_303; 
x_303 = lean_nat_dec_lt(x_300, x_302);
if (x_303 == 0)
{
lean_object* x_304; 
lean_inc(x_8);
x_304 = l_Lean_Meta_inferType(x_299, x_8, x_298);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = l_Lean_Expr_getAppNumArgsAux___main(x_305, x_293);
x_308 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_307);
x_309 = lean_mk_array(x_307, x_308);
x_310 = lean_unsigned_to_nat(1u);
x_311 = lean_nat_sub(x_307, x_310);
lean_dec(x_307);
x_312 = lean_unbox(x_301);
lean_dec(x_301);
x_313 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_294, x_300, x_312, x_302, x_305, x_309, x_311, x_8, x_306);
return x_313;
}
else
{
uint8_t x_314; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_294);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_304);
if (x_314 == 0)
{
return x_304;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_304, 0);
x_316 = lean_ctor_get(x_304, 1);
lean_inc(x_316);
lean_inc(x_315);
lean_dec(x_304);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_294);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_318 = l_Lean_Name_toString___closed__1;
x_319 = l_Lean_Name_toStringWithSep___main(x_318, x_2);
x_320 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_320, 0, x_319);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_320);
x_322 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_323 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
x_324 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_325 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_box(0);
x_327 = l_Lean_Meta_throwOther___rarg(x_325, x_326, x_8, x_298);
lean_dec(x_8);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
return x_327;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_327, 0);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_327);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
else
{
uint8_t x_338; 
lean_dec(x_294);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_338 = !lean_is_exclusive(x_295);
if (x_338 == 0)
{
return x_295;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_295, 0);
x_340 = lean_ctor_get(x_295, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_295);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_342 = !lean_is_exclusive(x_291);
if (x_342 == 0)
{
return x_291;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_291, 0);
x_344 = lean_ctor_get(x_291, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_291);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
case 7:
{
lean_object* x_346; 
lean_dec(x_7);
lean_inc(x_2);
x_346 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
lean_dec(x_346);
x_348 = lean_unsigned_to_nat(0u);
x_349 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_348);
lean_inc(x_2);
x_350 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_347);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_388; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
lean_dec(x_350);
x_354 = lean_ctor_get(x_351, 0);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_352, 1);
lean_inc(x_356);
lean_dec(x_352);
x_388 = lean_unbox(x_356);
if (x_388 == 0)
{
lean_object* x_389; 
x_389 = lean_array_get_size(x_6);
x_357 = x_389;
goto block_387;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_array_get_size(x_6);
x_391 = lean_unsigned_to_nat(1u);
x_392 = lean_nat_sub(x_390, x_391);
lean_dec(x_390);
x_357 = x_392;
goto block_387;
}
block_387:
{
uint8_t x_358; 
x_358 = lean_nat_dec_lt(x_355, x_357);
if (x_358 == 0)
{
lean_object* x_359; 
lean_inc(x_8);
x_359 = l_Lean_Meta_inferType(x_354, x_8, x_353);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = l_Lean_Expr_getAppNumArgsAux___main(x_360, x_348);
x_363 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_362);
x_364 = lean_mk_array(x_362, x_363);
x_365 = lean_unsigned_to_nat(1u);
x_366 = lean_nat_sub(x_362, x_365);
lean_dec(x_362);
x_367 = lean_unbox(x_356);
lean_dec(x_356);
x_368 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_349, x_355, x_367, x_357, x_360, x_364, x_366, x_8, x_361);
return x_368;
}
else
{
uint8_t x_369; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_349);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_359);
if (x_369 == 0)
{
return x_359;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_359, 0);
x_371 = lean_ctor_get(x_359, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_359);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_349);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_373 = l_Lean_Name_toString___closed__1;
x_374 = l_Lean_Name_toStringWithSep___main(x_373, x_2);
x_375 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_376, 0, x_375);
x_377 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_378 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_380 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_box(0);
x_382 = l_Lean_Meta_throwOther___rarg(x_380, x_381, x_8, x_353);
lean_dec(x_8);
x_383 = !lean_is_exclusive(x_382);
if (x_383 == 0)
{
return x_382;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_382, 0);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_382);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_349);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_350);
if (x_393 == 0)
{
return x_350;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_350, 0);
x_395 = lean_ctor_get(x_350, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_350);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_346);
if (x_397 == 0)
{
return x_346;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_346, 0);
x_399 = lean_ctor_get(x_346, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_346);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
case 8:
{
lean_object* x_401; 
lean_dec(x_7);
lean_inc(x_2);
x_401 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_401, 1);
lean_inc(x_402);
lean_dec(x_401);
x_403 = lean_unsigned_to_nat(0u);
x_404 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_403);
lean_inc(x_2);
x_405 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_402);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_443; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_409 = lean_ctor_get(x_406, 0);
lean_inc(x_409);
lean_dec(x_406);
x_410 = lean_ctor_get(x_407, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_407, 1);
lean_inc(x_411);
lean_dec(x_407);
x_443 = lean_unbox(x_411);
if (x_443 == 0)
{
lean_object* x_444; 
x_444 = lean_array_get_size(x_6);
x_412 = x_444;
goto block_442;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_array_get_size(x_6);
x_446 = lean_unsigned_to_nat(1u);
x_447 = lean_nat_sub(x_445, x_446);
lean_dec(x_445);
x_412 = x_447;
goto block_442;
}
block_442:
{
uint8_t x_413; 
x_413 = lean_nat_dec_lt(x_410, x_412);
if (x_413 == 0)
{
lean_object* x_414; 
lean_inc(x_8);
x_414 = l_Lean_Meta_inferType(x_409, x_8, x_408);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
lean_dec(x_414);
x_417 = l_Lean_Expr_getAppNumArgsAux___main(x_415, x_403);
x_418 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_417);
x_419 = lean_mk_array(x_417, x_418);
x_420 = lean_unsigned_to_nat(1u);
x_421 = lean_nat_sub(x_417, x_420);
lean_dec(x_417);
x_422 = lean_unbox(x_411);
lean_dec(x_411);
x_423 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_404, x_410, x_422, x_412, x_415, x_419, x_421, x_8, x_416);
return x_423;
}
else
{
uint8_t x_424; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_404);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_414);
if (x_424 == 0)
{
return x_414;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_414, 0);
x_426 = lean_ctor_get(x_414, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_414);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; 
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_404);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_428 = l_Lean_Name_toString___closed__1;
x_429 = l_Lean_Name_toStringWithSep___main(x_428, x_2);
x_430 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_430, 0, x_429);
x_431 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_433 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_431);
x_434 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_435 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_box(0);
x_437 = l_Lean_Meta_throwOther___rarg(x_435, x_436, x_8, x_408);
lean_dec(x_8);
x_438 = !lean_is_exclusive(x_437);
if (x_438 == 0)
{
return x_437;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_437, 0);
x_440 = lean_ctor_get(x_437, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_437);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_404);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_405);
if (x_448 == 0)
{
return x_405;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_405, 0);
x_450 = lean_ctor_get(x_405, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_405);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_401);
if (x_452 == 0)
{
return x_401;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_401, 0);
x_454 = lean_ctor_get(x_401, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_401);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
case 9:
{
lean_object* x_456; 
lean_dec(x_7);
lean_inc(x_2);
x_456 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
lean_dec(x_456);
x_458 = lean_unsigned_to_nat(0u);
x_459 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_458);
lean_inc(x_2);
x_460 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_457);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; uint8_t x_498; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_460, 1);
lean_inc(x_463);
lean_dec(x_460);
x_464 = lean_ctor_get(x_461, 0);
lean_inc(x_464);
lean_dec(x_461);
x_465 = lean_ctor_get(x_462, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_462, 1);
lean_inc(x_466);
lean_dec(x_462);
x_498 = lean_unbox(x_466);
if (x_498 == 0)
{
lean_object* x_499; 
x_499 = lean_array_get_size(x_6);
x_467 = x_499;
goto block_497;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_array_get_size(x_6);
x_501 = lean_unsigned_to_nat(1u);
x_502 = lean_nat_sub(x_500, x_501);
lean_dec(x_500);
x_467 = x_502;
goto block_497;
}
block_497:
{
uint8_t x_468; 
x_468 = lean_nat_dec_lt(x_465, x_467);
if (x_468 == 0)
{
lean_object* x_469; 
lean_inc(x_8);
x_469 = l_Lean_Meta_inferType(x_464, x_8, x_463);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; 
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_469, 1);
lean_inc(x_471);
lean_dec(x_469);
x_472 = l_Lean_Expr_getAppNumArgsAux___main(x_470, x_458);
x_473 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_472);
x_474 = lean_mk_array(x_472, x_473);
x_475 = lean_unsigned_to_nat(1u);
x_476 = lean_nat_sub(x_472, x_475);
lean_dec(x_472);
x_477 = lean_unbox(x_466);
lean_dec(x_466);
x_478 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_459, x_465, x_477, x_467, x_470, x_474, x_476, x_8, x_471);
return x_478;
}
else
{
uint8_t x_479; 
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_459);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_469);
if (x_479 == 0)
{
return x_469;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_469, 0);
x_481 = lean_ctor_get(x_469, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_469);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_459);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_483 = l_Lean_Name_toString___closed__1;
x_484 = l_Lean_Name_toStringWithSep___main(x_483, x_2);
x_485 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_486 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_486, 0, x_485);
x_487 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_488 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_486);
x_489 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_490 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_491 = lean_box(0);
x_492 = l_Lean_Meta_throwOther___rarg(x_490, x_491, x_8, x_463);
lean_dec(x_8);
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
return x_492;
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_492, 0);
x_495 = lean_ctor_get(x_492, 1);
lean_inc(x_495);
lean_inc(x_494);
lean_dec(x_492);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
return x_496;
}
}
}
}
else
{
uint8_t x_503; 
lean_dec(x_459);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_503 = !lean_is_exclusive(x_460);
if (x_503 == 0)
{
return x_460;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_460, 0);
x_505 = lean_ctor_get(x_460, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_460);
x_506 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
return x_506;
}
}
}
else
{
uint8_t x_507; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_507 = !lean_is_exclusive(x_456);
if (x_507 == 0)
{
return x_456;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_456, 0);
x_509 = lean_ctor_get(x_456, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_456);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
case 10:
{
lean_object* x_511; 
lean_dec(x_7);
lean_inc(x_2);
x_511 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_unsigned_to_nat(0u);
x_514 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_513);
lean_inc(x_2);
x_515 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_512);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_553; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
x_518 = lean_ctor_get(x_515, 1);
lean_inc(x_518);
lean_dec(x_515);
x_519 = lean_ctor_get(x_516, 0);
lean_inc(x_519);
lean_dec(x_516);
x_520 = lean_ctor_get(x_517, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_517, 1);
lean_inc(x_521);
lean_dec(x_517);
x_553 = lean_unbox(x_521);
if (x_553 == 0)
{
lean_object* x_554; 
x_554 = lean_array_get_size(x_6);
x_522 = x_554;
goto block_552;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_array_get_size(x_6);
x_556 = lean_unsigned_to_nat(1u);
x_557 = lean_nat_sub(x_555, x_556);
lean_dec(x_555);
x_522 = x_557;
goto block_552;
}
block_552:
{
uint8_t x_523; 
x_523 = lean_nat_dec_lt(x_520, x_522);
if (x_523 == 0)
{
lean_object* x_524; 
lean_inc(x_8);
x_524 = l_Lean_Meta_inferType(x_519, x_8, x_518);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; uint8_t x_532; lean_object* x_533; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = l_Lean_Expr_getAppNumArgsAux___main(x_525, x_513);
x_528 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_527);
x_529 = lean_mk_array(x_527, x_528);
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_sub(x_527, x_530);
lean_dec(x_527);
x_532 = lean_unbox(x_521);
lean_dec(x_521);
x_533 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_514, x_520, x_532, x_522, x_525, x_529, x_531, x_8, x_526);
return x_533;
}
else
{
uint8_t x_534; 
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_514);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_534 = !lean_is_exclusive(x_524);
if (x_534 == 0)
{
return x_524;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_524, 0);
x_536 = lean_ctor_get(x_524, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_524);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint8_t x_548; 
lean_dec(x_522);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_519);
lean_dec(x_514);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_538 = l_Lean_Name_toString___closed__1;
x_539 = l_Lean_Name_toStringWithSep___main(x_538, x_2);
x_540 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_540, 0, x_539);
x_541 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_541, 0, x_540);
x_542 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_543 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_541);
x_544 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_545 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_box(0);
x_547 = l_Lean_Meta_throwOther___rarg(x_545, x_546, x_8, x_518);
lean_dec(x_8);
x_548 = !lean_is_exclusive(x_547);
if (x_548 == 0)
{
return x_547;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_547, 0);
x_550 = lean_ctor_get(x_547, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_547);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_514);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_515);
if (x_558 == 0)
{
return x_515;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_515, 0);
x_560 = lean_ctor_get(x_515, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_515);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
uint8_t x_562; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_562 = !lean_is_exclusive(x_511);
if (x_562 == 0)
{
return x_511;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_511, 0);
x_564 = lean_ctor_get(x_511, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_511);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
case 11:
{
lean_object* x_566; 
lean_dec(x_7);
lean_inc(x_2);
x_566 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = lean_unsigned_to_nat(0u);
x_569 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_568);
lean_inc(x_2);
x_570 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_567);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_608; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_570, 1);
lean_inc(x_573);
lean_dec(x_570);
x_574 = lean_ctor_get(x_571, 0);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_ctor_get(x_572, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_572, 1);
lean_inc(x_576);
lean_dec(x_572);
x_608 = lean_unbox(x_576);
if (x_608 == 0)
{
lean_object* x_609; 
x_609 = lean_array_get_size(x_6);
x_577 = x_609;
goto block_607;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_array_get_size(x_6);
x_611 = lean_unsigned_to_nat(1u);
x_612 = lean_nat_sub(x_610, x_611);
lean_dec(x_610);
x_577 = x_612;
goto block_607;
}
block_607:
{
uint8_t x_578; 
x_578 = lean_nat_dec_lt(x_575, x_577);
if (x_578 == 0)
{
lean_object* x_579; 
lean_inc(x_8);
x_579 = l_Lean_Meta_inferType(x_574, x_8, x_573);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; lean_object* x_588; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_579, 1);
lean_inc(x_581);
lean_dec(x_579);
x_582 = l_Lean_Expr_getAppNumArgsAux___main(x_580, x_568);
x_583 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_582);
x_584 = lean_mk_array(x_582, x_583);
x_585 = lean_unsigned_to_nat(1u);
x_586 = lean_nat_sub(x_582, x_585);
lean_dec(x_582);
x_587 = lean_unbox(x_576);
lean_dec(x_576);
x_588 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_569, x_575, x_587, x_577, x_580, x_584, x_586, x_8, x_581);
return x_588;
}
else
{
uint8_t x_589; 
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_569);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_579);
if (x_589 == 0)
{
return x_579;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_579, 0);
x_591 = lean_ctor_get(x_579, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_579);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; 
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_569);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_593 = l_Lean_Name_toString___closed__1;
x_594 = l_Lean_Name_toStringWithSep___main(x_593, x_2);
x_595 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_595, 0, x_594);
x_596 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_596, 0, x_595);
x_597 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_598 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_596);
x_599 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_600 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_600, 0, x_598);
lean_ctor_set(x_600, 1, x_599);
x_601 = lean_box(0);
x_602 = l_Lean_Meta_throwOther___rarg(x_600, x_601, x_8, x_573);
lean_dec(x_8);
x_603 = !lean_is_exclusive(x_602);
if (x_603 == 0)
{
return x_602;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_602, 0);
x_605 = lean_ctor_get(x_602, 1);
lean_inc(x_605);
lean_inc(x_604);
lean_dec(x_602);
x_606 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
return x_606;
}
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_569);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_570);
if (x_613 == 0)
{
return x_570;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_570, 0);
x_615 = lean_ctor_get(x_570, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_570);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
else
{
uint8_t x_617; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_617 = !lean_is_exclusive(x_566);
if (x_617 == 0)
{
return x_566;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_566, 0);
x_619 = lean_ctor_get(x_566, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_566);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
default: 
{
lean_object* x_621; 
lean_dec(x_7);
lean_inc(x_2);
x_621 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_621, 1);
lean_inc(x_622);
lean_dec(x_621);
x_623 = lean_unsigned_to_nat(0u);
x_624 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_623);
lean_inc(x_2);
x_625 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_622);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_663; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_626, 1);
lean_inc(x_627);
x_628 = lean_ctor_get(x_625, 1);
lean_inc(x_628);
lean_dec(x_625);
x_629 = lean_ctor_get(x_626, 0);
lean_inc(x_629);
lean_dec(x_626);
x_630 = lean_ctor_get(x_627, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_627, 1);
lean_inc(x_631);
lean_dec(x_627);
x_663 = lean_unbox(x_631);
if (x_663 == 0)
{
lean_object* x_664; 
x_664 = lean_array_get_size(x_6);
x_632 = x_664;
goto block_662;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_array_get_size(x_6);
x_666 = lean_unsigned_to_nat(1u);
x_667 = lean_nat_sub(x_665, x_666);
lean_dec(x_665);
x_632 = x_667;
goto block_662;
}
block_662:
{
uint8_t x_633; 
x_633 = lean_nat_dec_lt(x_630, x_632);
if (x_633 == 0)
{
lean_object* x_634; 
lean_inc(x_8);
x_634 = l_Lean_Meta_inferType(x_629, x_8, x_628);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; uint8_t x_642; lean_object* x_643; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
lean_dec(x_634);
x_637 = l_Lean_Expr_getAppNumArgsAux___main(x_635, x_623);
x_638 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_637);
x_639 = lean_mk_array(x_637, x_638);
x_640 = lean_unsigned_to_nat(1u);
x_641 = lean_nat_sub(x_637, x_640);
lean_dec(x_637);
x_642 = lean_unbox(x_631);
lean_dec(x_631);
x_643 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_624, x_630, x_642, x_632, x_635, x_639, x_641, x_8, x_636);
return x_643;
}
else
{
uint8_t x_644; 
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_624);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_644 = !lean_is_exclusive(x_634);
if (x_644 == 0)
{
return x_634;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_634, 0);
x_646 = lean_ctor_get(x_634, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_634);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
return x_647;
}
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; 
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_630);
lean_dec(x_629);
lean_dec(x_624);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_648 = l_Lean_Name_toString___closed__1;
x_649 = l_Lean_Name_toStringWithSep___main(x_648, x_2);
x_650 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_650, 0, x_649);
x_651 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_651, 0, x_650);
x_652 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_653 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_651);
x_654 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___closed__3;
x_655 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
x_656 = lean_box(0);
x_657 = l_Lean_Meta_throwOther___rarg(x_655, x_656, x_8, x_628);
lean_dec(x_8);
x_658 = !lean_is_exclusive(x_657);
if (x_658 == 0)
{
return x_657;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_657, 0);
x_660 = lean_ctor_get(x_657, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_657);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
}
else
{
uint8_t x_668; 
lean_dec(x_624);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_668 = !lean_is_exclusive(x_625);
if (x_668 == 0)
{
return x_625;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_625, 0);
x_670 = lean_ctor_get(x_625, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_625);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
}
}
}
else
{
uint8_t x_672; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_672 = !lean_is_exclusive(x_621);
if (x_672 == 0)
{
return x_621;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_621, 0);
x_674 = lean_ctor_get(x_621, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_621);
x_675 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_675, 0, x_673);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
}
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Expr_getAppNumArgsAux___main(x_5, x_8);
x_10 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_9);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_9, x_12);
lean_dec(x_9);
x_14 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_13, x_6, x_7);
return x_14;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_5);
x_6 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_ConstantInfo_type(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed), 7, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
x_11 = l_Lean_Meta_forallTelescopeReducing___rarg(x_9, x_10, x_3, x_8);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_8);
lean_dec(x_8);
x_17 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
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
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getConstInfo(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_8, x_3, x_7);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_2, x_3, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l___private_Lean_Environment_5__envExtensionsRef;
x_14 = lean_io_ref_get(x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_19);
x_23 = x_19;
x_24 = lean_array_push(x_21, x_23);
x_25 = lean_io_ref_set(x_13, x_24, x_22);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
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
else
{
uint8_t x_30; 
lean_dec(x_19);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_19);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_14);
if (x_38 == 0)
{
return x_14;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_14, 0);
x_40 = lean_ctor_get(x_14, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_14);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_3);
if (x_42 == 0)
{
return x_3;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_3, 0);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_3);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Environment_8__persistentEnvExtensionsRef;
x_4 = lean_io_ref_get(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
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
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_22);
x_26 = x_22;
x_27 = lean_array_push(x_24, x_26);
x_28 = lean_io_ref_set(x_3, x_27, x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
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
lean_dec(x_22);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
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
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
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
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
return x_19;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_19);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = l_Lean_Name_toString___closed__1;
x_47 = l_Lean_Name_toStringWithSep___main(x_46, x_45);
x_48 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_49 = lean_string_append(x_48, x_47);
lean_dec(x_47);
x_50 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_52);
return x_4;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_4, 0);
x_54 = lean_ctor_get(x_4, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_4);
x_55 = lean_array_get_size(x_53);
x_56 = lean_unsigned_to_nat(0u);
x_57 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__7(x_1, x_53, x_53, x_55, x_56);
lean_dec(x_55);
lean_dec(x_53);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_1, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 4);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 5);
lean_inc(x_63);
lean_dec(x_1);
x_64 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_65 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_65, 0, x_59);
lean_closure_set(x_65, 1, x_64);
x_66 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__8(x_65, x_54);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_58);
lean_ctor_set(x_69, 2, x_60);
lean_ctor_set(x_69, 3, x_61);
lean_ctor_set(x_69, 4, x_62);
lean_ctor_set(x_69, 5, x_63);
x_70 = lean_io_ref_take(x_3, x_68);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_69);
x_73 = x_69;
x_74 = lean_array_push(x_71, x_73);
x_75 = lean_io_ref_set(x_3, x_74, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_69);
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_81 = x_75;
} else {
 lean_dec_ref(x_75);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_69);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_85 = x_70;
} else {
 lean_dec_ref(x_70);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
x_87 = lean_ctor_get(x_66, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_66, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_89 = x_66;
} else {
 lean_dec_ref(x_66);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
lean_dec(x_1);
x_92 = l_Lean_Name_toString___closed__1;
x_93 = l_Lean_Name_toStringWithSep___main(x_92, x_91);
x_94 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_95 = lean_string_append(x_94, x_93);
lean_dec(x_93);
x_96 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_97 = lean_string_append(x_95, x_96);
x_98 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_54);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_4);
if (x_100 == 0)
{
return x_4;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_4, 0);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_4);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
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
lean_object* _init_l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_run___rarg___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_defaultMaxRecDepth;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Core_getEnv___rarg(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_MetavarContext_Inhabited___closed__1;
x_11 = l_Lean_Meta_run___rarg___closed__5;
x_12 = l_Lean_NameGenerator_Inhabited___closed__3;
x_13 = l_Lean_TraceState_Inhabited___closed__1;
x_14 = l_Std_PersistentArray_empty___closed__3;
x_15 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_11);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_14);
x_16 = l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1;
x_17 = l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(x_1, x_9, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(x_20, x_8);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = l_Lean_Core_setEnv(x_23, x_3, x_4, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_21, 0, x_27);
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_ctor_get(x_33, 4);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Std_PersistentArray_forM___at_IO_runMeta___spec__1(x_35, x_8);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
x_39 = l_Lean_Meta_Exception_toStr(x_32);
x_40 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l_Lean_Meta_Exception_toStr(x_32);
x_44 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_32);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_36, 0, x_49);
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_6);
if (x_54 == 0)
{
return x_6;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorAttr___lambda__2___boxed), 5, 0);
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
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_mkRecursorAttr___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getConstInfo(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_14, x_3, x_7);
lean_dec(x_3);
return x_15;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_2, x_3, x_7);
return x_17;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Lean_Meta_recursorAttribute;
x_11 = l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(x_10, x_9, x_1);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_11, x_3, x_7);
return x_12;
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
return x_5;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
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
res = initialize_Lean_Meta_Message(lean_io_mk_world());
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
l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1 = _init_l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_mkRecursorAttr___lambda__2___closed__1);
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
