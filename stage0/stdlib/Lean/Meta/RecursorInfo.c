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
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
lean_object* l_List_range(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__6;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__5;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23;
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__9;
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__3;
extern lean_object* l___private_Lean_Environment_8__persistentEnvExtensionsRef;
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__8;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22;
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
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__13;
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__5;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__2;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__8;
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__9;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Meta_run___rarg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
extern lean_object* l___private_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Array_findIdxMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1___boxed(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__3;
lean_object* l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__12;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__8;
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerParametricAttribute___spec__9___rarg___closed__1;
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__10;
lean_object* l___private_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__7;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l___private_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
lean_object* l_List_map___main___at___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__15;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__3;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__2;
lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__2;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_recOnSuffix___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1(lean_object*);
lean_object* l___private_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
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
lean_object* _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__3;
x_2 = lean_alloc_ctor(22, 1, 0);
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
uint8_t x_79; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_6);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_6, 0);
lean_dec(x_80);
x_81 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4;
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_81);
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
lean_dec(x_6);
x_83 = l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4;
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_6);
if (x_85 == 0)
{
return x_6;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_6, 0);
x_87 = lean_ctor_get(x_6, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_6);
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
lean_object* _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3;
x_2 = lean_alloc_ctor(22, 1, 0);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_57; uint8_t x_58; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_57 = l_Lean_Meta_recOnSuffix;
x_58 = lean_string_dec_eq(x_11, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Meta_casesOnSuffix;
x_60 = lean_string_dec_eq(x_11, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Meta_brecOnSuffix;
x_62 = lean_string_dec_eq(x_11, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_11);
lean_dec(x_10);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_4);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_12 = x_65;
goto block_56;
}
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_12 = x_66;
goto block_56;
}
}
else
{
lean_object* x_67; 
x_67 = lean_box(0);
x_12 = x_67;
goto block_56;
}
block_56:
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
uint8_t x_46; 
lean_dec(x_16);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_15, 0);
lean_dec(x_47);
x_48 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4;
lean_ctor_set_tag(x_15, 1);
lean_ctor_set(x_15, 0, x_48);
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_dec(x_15);
x_50 = l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4;
x_51 = lean_alloc_ctor(1, 2, 0);
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
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_2);
lean_ctor_set(x_70, 1, x_4);
return x_70;
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
x_17 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
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
x_34 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid user defined recursor, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("and position of the major premise was not specified ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__15;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__16;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid major premise position for user defined recursor, recursor has only ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" arguments");
return x_1;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22;
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
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Array_isEmpty___rarg(x_5);
x_9 = l_Array_back___at___private_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_findIdxAux___main___at___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_9, x_3, x_10);
if (x_8 == 0)
{
uint8_t x_44; 
x_44 = 0;
x_12 = x_44;
goto block_43;
}
else
{
uint8_t x_45; 
x_45 = 1;
x_12 = x_45;
goto block_43;
}
block_43:
{
if (x_12 == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_1);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_7);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_9);
x_29 = l_Lean_Name_toString___closed__1;
x_30 = l_Lean_Name_toStringWithSep___main(x_29, x_1);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__8;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__11;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__14;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__17;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_7);
return x_42;
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
x_52 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__20;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_7);
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
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Lean_LocalDecl_binderInfo(x_23);
lean_dec(x_23);
x_26 = l_Lean_BinderInfo_isInstImplicit(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
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
x_33 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_35);
return x_21;
}
else
{
lean_object* x_36; 
lean_free_object(x_21);
x_36 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_36;
x_8 = x_24;
goto _start;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = l_Lean_LocalDecl_binderInfo(x_38);
lean_dec(x_38);
x_41 = l_Lean_BinderInfo_isInstImplicit(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_42 = l_Lean_Name_toString___closed__1;
x_43 = l_Lean_Name_toStringWithSep___main(x_42, x_1);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_39);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_52;
x_8 = x_39;
goto _start;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_21);
if (x_54 == 0)
{
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_21, 0);
x_56 = lean_ctor_get(x_21, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_21);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_16);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_dec(x_17);
x_59 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_59;
x_8 = x_58;
goto _start;
}
}
else
{
uint8_t x_61; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
return x_17;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_17, 0);
x_63 = lean_ctor_get(x_17, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_17);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_8);
return x_65;
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
uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
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
x_31 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = l_Lean_Name_toString___closed__1;
x_36 = l_Lean_Name_toStringWithSep___main(x_35, x_1);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Nat_foldMAux___main___at___private_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_dec(x_21);
x_46 = lean_ctor_get(x_22, 0);
lean_inc(x_46);
lean_dec(x_22);
x_47 = lean_array_push(x_8, x_46);
x_7 = x_14;
x_8 = x_47;
x_10 = x_45;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_21);
if (x_49 == 0)
{
return x_21;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_21, 0);
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_10);
return x_53;
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
x_14 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
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
x_27 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
x_31 = lean_ctor_get(x_14, 0);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_array_push(x_4, x_32);
x_4 = x_33;
x_5 = x_10;
goto _start;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_9);
x_35 = lean_box(0);
x_36 = lean_array_push(x_4, x_35);
x_4 = x_36;
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
x_20 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
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
x_37 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_6);
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
lean_dec(x_13);
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
x_55 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_14);
return x_56;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', indices must occur before major premise");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_10);
lean_inc(x_2);
x_12 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_49; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_dec(x_16);
x_49 = lean_unbox(x_21);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_array_get_size(x_6);
x_22 = x_50;
goto block_48;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_array_get_size(x_6);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
lean_dec(x_51);
x_22 = x_53;
goto block_48;
}
block_48:
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_20, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
lean_inc(x_8);
x_24 = l_Lean_Meta_inferType(x_19, x_8, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_10);
x_28 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = lean_unbox(x_21);
lean_dec(x_21);
x_33 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_11, x_20, x_32, x_22, x_25, x_29, x_31, x_8, x_26);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
return x_24;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_2);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_18)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_18;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
return x_47;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
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
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_12);
if (x_58 == 0)
{
return x_12;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_12, 0);
x_60 = lean_ctor_get(x_12, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_12);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
case 1:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_62);
lean_inc(x_2);
x_64 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
lean_inc(x_2);
x_66 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_101; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_101 = lean_unbox(x_73);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_array_get_size(x_6);
x_74 = x_102;
goto block_100;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_array_get_size(x_6);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_103, x_104);
lean_dec(x_103);
x_74 = x_105;
goto block_100;
}
block_100:
{
uint8_t x_75; 
x_75 = lean_nat_dec_lt(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_70);
lean_inc(x_8);
x_76 = l_Lean_Meta_inferType(x_71, x_8, x_69);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Expr_getAppNumArgsAux___main(x_77, x_62);
x_80 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_79);
x_81 = lean_mk_array(x_79, x_80);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_79, x_82);
lean_dec(x_79);
x_84 = lean_unbox(x_73);
lean_dec(x_73);
x_85 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_63, x_72, x_84, x_74, x_77, x_81, x_83, x_8, x_78);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_90 = l_Lean_Name_toString___closed__1;
x_91 = l_Lean_Name_toStringWithSep___main(x_90, x_2);
x_92 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_98, 0, x_97);
if (lean_is_scalar(x_70)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_70;
 lean_ctor_set_tag(x_99, 1);
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_69);
return x_99;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_66);
if (x_106 == 0)
{
return x_66;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_66, 0);
x_108 = lean_ctor_get(x_66, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_66);
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
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_64);
if (x_110 == 0)
{
return x_64;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_64, 0);
x_112 = lean_ctor_get(x_64, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_64);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_7);
x_114 = lean_unsigned_to_nat(0u);
x_115 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_114);
lean_inc(x_2);
x_116 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_2);
x_118 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_153; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_122 = x_118;
} else {
 lean_dec_ref(x_118);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
lean_dec(x_119);
x_124 = lean_ctor_get(x_120, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_153 = lean_unbox(x_125);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_array_get_size(x_6);
x_126 = x_154;
goto block_152;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_array_get_size(x_6);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_nat_sub(x_155, x_156);
lean_dec(x_155);
x_126 = x_157;
goto block_152;
}
block_152:
{
uint8_t x_127; 
x_127 = lean_nat_dec_lt(x_124, x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_122);
lean_inc(x_8);
x_128 = l_Lean_Meta_inferType(x_123, x_8, x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Expr_getAppNumArgsAux___main(x_129, x_114);
x_132 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_131);
x_133 = lean_mk_array(x_131, x_132);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_sub(x_131, x_134);
lean_dec(x_131);
x_136 = lean_unbox(x_125);
lean_dec(x_125);
x_137 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_115, x_124, x_136, x_126, x_129, x_133, x_135, x_8, x_130);
return x_137;
}
else
{
uint8_t x_138; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_115);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_128);
if (x_138 == 0)
{
return x_128;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_128, 0);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_128);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_115);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_142 = l_Lean_Name_toString___closed__1;
x_143 = l_Lean_Name_toStringWithSep___main(x_142, x_2);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_147 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
x_148 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_149 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_150, 0, x_149);
if (lean_is_scalar(x_122)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_122;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_121);
return x_151;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_115);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_118);
if (x_158 == 0)
{
return x_118;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_118, 0);
x_160 = lean_ctor_get(x_118, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_118);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_115);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_116);
if (x_162 == 0)
{
return x_116;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_116, 0);
x_164 = lean_ctor_get(x_116, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_116);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
case 3:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_7);
x_166 = lean_unsigned_to_nat(0u);
x_167 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_166);
lean_inc(x_2);
x_168 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
lean_inc(x_2);
x_170 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_205; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_171, 0);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
lean_dec(x_172);
x_205 = lean_unbox(x_177);
if (x_205 == 0)
{
lean_object* x_206; 
x_206 = lean_array_get_size(x_6);
x_178 = x_206;
goto block_204;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_array_get_size(x_6);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_nat_sub(x_207, x_208);
lean_dec(x_207);
x_178 = x_209;
goto block_204;
}
block_204:
{
uint8_t x_179; 
x_179 = lean_nat_dec_lt(x_176, x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_174);
lean_inc(x_8);
x_180 = l_Lean_Meta_inferType(x_175, x_8, x_173);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
x_183 = l_Lean_Expr_getAppNumArgsAux___main(x_181, x_166);
x_184 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_183);
x_185 = lean_mk_array(x_183, x_184);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_sub(x_183, x_186);
lean_dec(x_183);
x_188 = lean_unbox(x_177);
lean_dec(x_177);
x_189 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_167, x_176, x_188, x_178, x_181, x_185, x_187, x_8, x_182);
return x_189;
}
else
{
uint8_t x_190; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_167);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_180);
if (x_190 == 0)
{
return x_180;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_180, 0);
x_192 = lean_ctor_get(x_180, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_180);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_167);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_194 = l_Lean_Name_toString___closed__1;
x_195 = l_Lean_Name_toStringWithSep___main(x_194, x_2);
x_196 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_199 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_197);
x_200 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_201 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_202, 0, x_201);
if (lean_is_scalar(x_174)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_174;
 lean_ctor_set_tag(x_203, 1);
}
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_173);
return x_203;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_167);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_170);
if (x_210 == 0)
{
return x_170;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_170, 0);
x_212 = lean_ctor_get(x_170, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_170);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_167);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_168);
if (x_214 == 0)
{
return x_168;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_168, 0);
x_216 = lean_ctor_get(x_168, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_168);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
case 4:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_7);
x_218 = lean_unsigned_to_nat(0u);
x_219 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_218);
lean_inc(x_2);
x_220 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
lean_inc(x_2);
x_222 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_257; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 0);
lean_inc(x_227);
lean_dec(x_223);
x_228 = lean_ctor_get(x_224, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_dec(x_224);
x_257 = lean_unbox(x_229);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_array_get_size(x_6);
x_230 = x_258;
goto block_256;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_array_get_size(x_6);
x_260 = lean_unsigned_to_nat(1u);
x_261 = lean_nat_sub(x_259, x_260);
lean_dec(x_259);
x_230 = x_261;
goto block_256;
}
block_256:
{
uint8_t x_231; 
x_231 = lean_nat_dec_lt(x_228, x_230);
if (x_231 == 0)
{
lean_object* x_232; 
lean_dec(x_226);
lean_inc(x_8);
x_232 = l_Lean_Meta_inferType(x_227, x_8, x_225);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_Lean_Expr_getAppNumArgsAux___main(x_233, x_218);
x_236 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_235);
x_237 = lean_mk_array(x_235, x_236);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_sub(x_235, x_238);
lean_dec(x_235);
x_240 = lean_unbox(x_229);
lean_dec(x_229);
x_241 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_219, x_228, x_240, x_230, x_233, x_237, x_239, x_8, x_234);
return x_241;
}
else
{
uint8_t x_242; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_232);
if (x_242 == 0)
{
return x_232;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_232, 0);
x_244 = lean_ctor_get(x_232, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_232);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_246 = l_Lean_Name_toString___closed__1;
x_247 = l_Lean_Name_toStringWithSep___main(x_246, x_2);
x_248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_251 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_253 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_254 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_254, 0, x_253);
if (lean_is_scalar(x_226)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_226;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_225);
return x_255;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_222);
if (x_262 == 0)
{
return x_222;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_222, 0);
x_264 = lean_ctor_get(x_222, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_222);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_220);
if (x_266 == 0)
{
return x_220;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_220, 0);
x_268 = lean_ctor_get(x_220, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_220);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
case 5:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_270 = lean_ctor_get(x_5, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_5, 1);
lean_inc(x_271);
lean_dec(x_5);
x_272 = lean_array_set(x_6, x_7, x_271);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_sub(x_7, x_273);
lean_dec(x_7);
x_5 = x_270;
x_6 = x_272;
x_7 = x_274;
goto _start;
}
case 6:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_7);
x_276 = lean_unsigned_to_nat(0u);
x_277 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_276);
lean_inc(x_2);
x_278 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
lean_inc(x_2);
x_280 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_315; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_284 = x_280;
} else {
 lean_dec_ref(x_280);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_ctor_get(x_282, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_282, 1);
lean_inc(x_287);
lean_dec(x_282);
x_315 = lean_unbox(x_287);
if (x_315 == 0)
{
lean_object* x_316; 
x_316 = lean_array_get_size(x_6);
x_288 = x_316;
goto block_314;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_array_get_size(x_6);
x_318 = lean_unsigned_to_nat(1u);
x_319 = lean_nat_sub(x_317, x_318);
lean_dec(x_317);
x_288 = x_319;
goto block_314;
}
block_314:
{
uint8_t x_289; 
x_289 = lean_nat_dec_lt(x_286, x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_284);
lean_inc(x_8);
x_290 = l_Lean_Meta_inferType(x_285, x_8, x_283);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; 
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_290, 1);
lean_inc(x_292);
lean_dec(x_290);
x_293 = l_Lean_Expr_getAppNumArgsAux___main(x_291, x_276);
x_294 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_293);
x_295 = lean_mk_array(x_293, x_294);
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_nat_sub(x_293, x_296);
lean_dec(x_293);
x_298 = lean_unbox(x_287);
lean_dec(x_287);
x_299 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_277, x_286, x_298, x_288, x_291, x_295, x_297, x_8, x_292);
return x_299;
}
else
{
uint8_t x_300; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_277);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_300 = !lean_is_exclusive(x_290);
if (x_300 == 0)
{
return x_290;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_290, 0);
x_302 = lean_ctor_get(x_290, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_290);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_277);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_304 = l_Lean_Name_toString___closed__1;
x_305 = l_Lean_Name_toStringWithSep___main(x_304, x_2);
x_306 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_307 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_309 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_307);
x_310 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_311 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_312, 0, x_311);
if (lean_is_scalar(x_284)) {
 x_313 = lean_alloc_ctor(1, 2, 0);
} else {
 x_313 = x_284;
 lean_ctor_set_tag(x_313, 1);
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_283);
return x_313;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_277);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_280);
if (x_320 == 0)
{
return x_280;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_280, 0);
x_322 = lean_ctor_get(x_280, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_280);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_277);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_278);
if (x_324 == 0)
{
return x_278;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_278, 0);
x_326 = lean_ctor_get(x_278, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_278);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
case 7:
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_7);
x_328 = lean_unsigned_to_nat(0u);
x_329 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_328);
lean_inc(x_2);
x_330 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
lean_inc(x_2);
x_332 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_367; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
x_335 = lean_ctor_get(x_332, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 lean_ctor_release(x_332, 1);
 x_336 = x_332;
} else {
 lean_dec_ref(x_332);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_333, 0);
lean_inc(x_337);
lean_dec(x_333);
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_334, 1);
lean_inc(x_339);
lean_dec(x_334);
x_367 = lean_unbox(x_339);
if (x_367 == 0)
{
lean_object* x_368; 
x_368 = lean_array_get_size(x_6);
x_340 = x_368;
goto block_366;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_array_get_size(x_6);
x_370 = lean_unsigned_to_nat(1u);
x_371 = lean_nat_sub(x_369, x_370);
lean_dec(x_369);
x_340 = x_371;
goto block_366;
}
block_366:
{
uint8_t x_341; 
x_341 = lean_nat_dec_lt(x_338, x_340);
if (x_341 == 0)
{
lean_object* x_342; 
lean_dec(x_336);
lean_inc(x_8);
x_342 = l_Lean_Meta_inferType(x_337, x_8, x_335);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lean_Expr_getAppNumArgsAux___main(x_343, x_328);
x_346 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_345);
x_347 = lean_mk_array(x_345, x_346);
x_348 = lean_unsigned_to_nat(1u);
x_349 = lean_nat_sub(x_345, x_348);
lean_dec(x_345);
x_350 = lean_unbox(x_339);
lean_dec(x_339);
x_351 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_329, x_338, x_350, x_340, x_343, x_347, x_349, x_8, x_344);
return x_351;
}
else
{
uint8_t x_352; 
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_329);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_352 = !lean_is_exclusive(x_342);
if (x_352 == 0)
{
return x_342;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_342, 0);
x_354 = lean_ctor_get(x_342, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_342);
x_355 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_329);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_356 = l_Lean_Name_toString___closed__1;
x_357 = l_Lean_Name_toStringWithSep___main(x_356, x_2);
x_358 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_358, 0, x_357);
x_359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_359, 0, x_358);
x_360 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_361 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
x_362 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_363 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_364, 0, x_363);
if (lean_is_scalar(x_336)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_336;
 lean_ctor_set_tag(x_365, 1);
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_335);
return x_365;
}
}
}
else
{
uint8_t x_372; 
lean_dec(x_329);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_372 = !lean_is_exclusive(x_332);
if (x_372 == 0)
{
return x_332;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_332, 0);
x_374 = lean_ctor_get(x_332, 1);
lean_inc(x_374);
lean_inc(x_373);
lean_dec(x_332);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
return x_375;
}
}
}
else
{
uint8_t x_376; 
lean_dec(x_329);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_330);
if (x_376 == 0)
{
return x_330;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_330, 0);
x_378 = lean_ctor_get(x_330, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_330);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
case 8:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_7);
x_380 = lean_unsigned_to_nat(0u);
x_381 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_380);
lean_inc(x_2);
x_382 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_382, 1);
lean_inc(x_383);
lean_dec(x_382);
lean_inc(x_2);
x_384 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; uint8_t x_419; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_384, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_388 = x_384;
} else {
 lean_dec_ref(x_384);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
lean_dec(x_385);
x_390 = lean_ctor_get(x_386, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_386, 1);
lean_inc(x_391);
lean_dec(x_386);
x_419 = lean_unbox(x_391);
if (x_419 == 0)
{
lean_object* x_420; 
x_420 = lean_array_get_size(x_6);
x_392 = x_420;
goto block_418;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_array_get_size(x_6);
x_422 = lean_unsigned_to_nat(1u);
x_423 = lean_nat_sub(x_421, x_422);
lean_dec(x_421);
x_392 = x_423;
goto block_418;
}
block_418:
{
uint8_t x_393; 
x_393 = lean_nat_dec_lt(x_390, x_392);
if (x_393 == 0)
{
lean_object* x_394; 
lean_dec(x_388);
lean_inc(x_8);
x_394 = l_Lean_Meta_inferType(x_389, x_8, x_387);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = l_Lean_Expr_getAppNumArgsAux___main(x_395, x_380);
x_398 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_397);
x_399 = lean_mk_array(x_397, x_398);
x_400 = lean_unsigned_to_nat(1u);
x_401 = lean_nat_sub(x_397, x_400);
lean_dec(x_397);
x_402 = lean_unbox(x_391);
lean_dec(x_391);
x_403 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_381, x_390, x_402, x_392, x_395, x_399, x_401, x_8, x_396);
return x_403;
}
else
{
uint8_t x_404; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_404 = !lean_is_exclusive(x_394);
if (x_404 == 0)
{
return x_394;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_394, 0);
x_406 = lean_ctor_get(x_394, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_394);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_408 = l_Lean_Name_toString___closed__1;
x_409 = l_Lean_Name_toStringWithSep___main(x_408, x_2);
x_410 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_412 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_413 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_415 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
x_416 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_416, 0, x_415);
if (lean_is_scalar(x_388)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_388;
 lean_ctor_set_tag(x_417, 1);
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_387);
return x_417;
}
}
}
else
{
uint8_t x_424; 
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_384);
if (x_424 == 0)
{
return x_384;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_384, 0);
x_426 = lean_ctor_get(x_384, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_384);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
else
{
uint8_t x_428; 
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_428 = !lean_is_exclusive(x_382);
if (x_428 == 0)
{
return x_382;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_382, 0);
x_430 = lean_ctor_get(x_382, 1);
lean_inc(x_430);
lean_inc(x_429);
lean_dec(x_382);
x_431 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
}
}
case 9:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_7);
x_432 = lean_unsigned_to_nat(0u);
x_433 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_432);
lean_inc(x_2);
x_434 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
lean_inc(x_2);
x_436 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_435);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_471; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_436, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_436)) {
 lean_ctor_release(x_436, 0);
 lean_ctor_release(x_436, 1);
 x_440 = x_436;
} else {
 lean_dec_ref(x_436);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_437, 0);
lean_inc(x_441);
lean_dec(x_437);
x_442 = lean_ctor_get(x_438, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_438, 1);
lean_inc(x_443);
lean_dec(x_438);
x_471 = lean_unbox(x_443);
if (x_471 == 0)
{
lean_object* x_472; 
x_472 = lean_array_get_size(x_6);
x_444 = x_472;
goto block_470;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_array_get_size(x_6);
x_474 = lean_unsigned_to_nat(1u);
x_475 = lean_nat_sub(x_473, x_474);
lean_dec(x_473);
x_444 = x_475;
goto block_470;
}
block_470:
{
uint8_t x_445; 
x_445 = lean_nat_dec_lt(x_442, x_444);
if (x_445 == 0)
{
lean_object* x_446; 
lean_dec(x_440);
lean_inc(x_8);
x_446 = l_Lean_Meta_inferType(x_441, x_8, x_439);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_449 = l_Lean_Expr_getAppNumArgsAux___main(x_447, x_432);
x_450 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_449);
x_451 = lean_mk_array(x_449, x_450);
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_nat_sub(x_449, x_452);
lean_dec(x_449);
x_454 = lean_unbox(x_443);
lean_dec(x_443);
x_455 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_433, x_442, x_454, x_444, x_447, x_451, x_453, x_8, x_448);
return x_455;
}
else
{
uint8_t x_456; 
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_433);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_446);
if (x_456 == 0)
{
return x_446;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_446, 0);
x_458 = lean_ctor_get(x_446, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_446);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_433);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_460 = l_Lean_Name_toString___closed__1;
x_461 = l_Lean_Name_toStringWithSep___main(x_460, x_2);
x_462 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_463 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_465 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
x_466 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_467 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_467, 0, x_465);
lean_ctor_set(x_467, 1, x_466);
x_468 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_468, 0, x_467);
if (lean_is_scalar(x_440)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_440;
 lean_ctor_set_tag(x_469, 1);
}
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_439);
return x_469;
}
}
}
else
{
uint8_t x_476; 
lean_dec(x_433);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_476 = !lean_is_exclusive(x_436);
if (x_476 == 0)
{
return x_436;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_436, 0);
x_478 = lean_ctor_get(x_436, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_436);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_433);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_434);
if (x_480 == 0)
{
return x_434;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_434, 0);
x_482 = lean_ctor_get(x_434, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_434);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
case 10:
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_7);
x_484 = lean_unsigned_to_nat(0u);
x_485 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_484);
lean_inc(x_2);
x_486 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
lean_inc(x_2);
x_488 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; uint8_t x_523; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_488, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_492 = x_488;
} else {
 lean_dec_ref(x_488);
 x_492 = lean_box(0);
}
x_493 = lean_ctor_get(x_489, 0);
lean_inc(x_493);
lean_dec(x_489);
x_494 = lean_ctor_get(x_490, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_490, 1);
lean_inc(x_495);
lean_dec(x_490);
x_523 = lean_unbox(x_495);
if (x_523 == 0)
{
lean_object* x_524; 
x_524 = lean_array_get_size(x_6);
x_496 = x_524;
goto block_522;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_array_get_size(x_6);
x_526 = lean_unsigned_to_nat(1u);
x_527 = lean_nat_sub(x_525, x_526);
lean_dec(x_525);
x_496 = x_527;
goto block_522;
}
block_522:
{
uint8_t x_497; 
x_497 = lean_nat_dec_lt(x_494, x_496);
if (x_497 == 0)
{
lean_object* x_498; 
lean_dec(x_492);
lean_inc(x_8);
x_498 = l_Lean_Meta_inferType(x_493, x_8, x_491);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = l_Lean_Expr_getAppNumArgsAux___main(x_499, x_484);
x_502 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_501);
x_503 = lean_mk_array(x_501, x_502);
x_504 = lean_unsigned_to_nat(1u);
x_505 = lean_nat_sub(x_501, x_504);
lean_dec(x_501);
x_506 = lean_unbox(x_495);
lean_dec(x_495);
x_507 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_485, x_494, x_506, x_496, x_499, x_503, x_505, x_8, x_500);
return x_507;
}
else
{
uint8_t x_508; 
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_494);
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_508 = !lean_is_exclusive(x_498);
if (x_508 == 0)
{
return x_498;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_498, 0);
x_510 = lean_ctor_get(x_498, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_498);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_496);
lean_dec(x_495);
lean_dec(x_494);
lean_dec(x_493);
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_512 = l_Lean_Name_toString___closed__1;
x_513 = l_Lean_Name_toStringWithSep___main(x_512, x_2);
x_514 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_514, 0, x_513);
x_515 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_515, 0, x_514);
x_516 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_517 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_515);
x_518 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_519 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_520, 0, x_519);
if (lean_is_scalar(x_492)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_492;
 lean_ctor_set_tag(x_521, 1);
}
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_491);
return x_521;
}
}
}
else
{
uint8_t x_528; 
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_528 = !lean_is_exclusive(x_488);
if (x_528 == 0)
{
return x_488;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_529 = lean_ctor_get(x_488, 0);
x_530 = lean_ctor_get(x_488, 1);
lean_inc(x_530);
lean_inc(x_529);
lean_dec(x_488);
x_531 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
return x_531;
}
}
}
else
{
uint8_t x_532; 
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_532 = !lean_is_exclusive(x_486);
if (x_532 == 0)
{
return x_486;
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_533 = lean_ctor_get(x_486, 0);
x_534 = lean_ctor_get(x_486, 1);
lean_inc(x_534);
lean_inc(x_533);
lean_dec(x_486);
x_535 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
return x_535;
}
}
}
case 11:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_7);
x_536 = lean_unsigned_to_nat(0u);
x_537 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_536);
lean_inc(x_2);
x_538 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
lean_dec(x_538);
lean_inc(x_2);
x_540 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_539);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; uint8_t x_575; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_544 = x_540;
} else {
 lean_dec_ref(x_540);
 x_544 = lean_box(0);
}
x_545 = lean_ctor_get(x_541, 0);
lean_inc(x_545);
lean_dec(x_541);
x_546 = lean_ctor_get(x_542, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_542, 1);
lean_inc(x_547);
lean_dec(x_542);
x_575 = lean_unbox(x_547);
if (x_575 == 0)
{
lean_object* x_576; 
x_576 = lean_array_get_size(x_6);
x_548 = x_576;
goto block_574;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_array_get_size(x_6);
x_578 = lean_unsigned_to_nat(1u);
x_579 = lean_nat_sub(x_577, x_578);
lean_dec(x_577);
x_548 = x_579;
goto block_574;
}
block_574:
{
uint8_t x_549; 
x_549 = lean_nat_dec_lt(x_546, x_548);
if (x_549 == 0)
{
lean_object* x_550; 
lean_dec(x_544);
lean_inc(x_8);
x_550 = l_Lean_Meta_inferType(x_545, x_8, x_543);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; lean_object* x_559; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = l_Lean_Expr_getAppNumArgsAux___main(x_551, x_536);
x_554 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_553);
x_555 = lean_mk_array(x_553, x_554);
x_556 = lean_unsigned_to_nat(1u);
x_557 = lean_nat_sub(x_553, x_556);
lean_dec(x_553);
x_558 = lean_unbox(x_547);
lean_dec(x_547);
x_559 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_537, x_546, x_558, x_548, x_551, x_555, x_557, x_8, x_552);
return x_559;
}
else
{
uint8_t x_560; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_537);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_550);
if (x_560 == 0)
{
return x_550;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_550, 0);
x_562 = lean_ctor_get(x_550, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_550);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_537);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_564 = l_Lean_Name_toString___closed__1;
x_565 = l_Lean_Name_toStringWithSep___main(x_564, x_2);
x_566 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_566, 0, x_565);
x_567 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_567, 0, x_566);
x_568 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_569 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_567);
x_570 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_571 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_572, 0, x_571);
if (lean_is_scalar(x_544)) {
 x_573 = lean_alloc_ctor(1, 2, 0);
} else {
 x_573 = x_544;
 lean_ctor_set_tag(x_573, 1);
}
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_543);
return x_573;
}
}
}
else
{
uint8_t x_580; 
lean_dec(x_537);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_580 = !lean_is_exclusive(x_540);
if (x_580 == 0)
{
return x_540;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_540, 0);
x_582 = lean_ctor_get(x_540, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_540);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_581);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_537);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_538);
if (x_584 == 0)
{
return x_538;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_538, 0);
x_586 = lean_ctor_get(x_538, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_538);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
default: 
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_7);
x_588 = lean_unsigned_to_nat(0u);
x_589 = l___private_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_588);
lean_inc(x_2);
x_590 = l___private_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
lean_dec(x_590);
lean_inc(x_2);
x_592 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_591);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_627; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
x_595 = lean_ctor_get(x_592, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_596 = x_592;
} else {
 lean_dec_ref(x_592);
 x_596 = lean_box(0);
}
x_597 = lean_ctor_get(x_593, 0);
lean_inc(x_597);
lean_dec(x_593);
x_598 = lean_ctor_get(x_594, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_594, 1);
lean_inc(x_599);
lean_dec(x_594);
x_627 = lean_unbox(x_599);
if (x_627 == 0)
{
lean_object* x_628; 
x_628 = lean_array_get_size(x_6);
x_600 = x_628;
goto block_626;
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_array_get_size(x_6);
x_630 = lean_unsigned_to_nat(1u);
x_631 = lean_nat_sub(x_629, x_630);
lean_dec(x_629);
x_600 = x_631;
goto block_626;
}
block_626:
{
uint8_t x_601; 
x_601 = lean_nat_dec_lt(x_598, x_600);
if (x_601 == 0)
{
lean_object* x_602; 
lean_dec(x_596);
lean_inc(x_8);
x_602 = l_Lean_Meta_inferType(x_597, x_8, x_595);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
x_605 = l_Lean_Expr_getAppNumArgsAux___main(x_603, x_588);
x_606 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_605);
x_607 = lean_mk_array(x_605, x_606);
x_608 = lean_unsigned_to_nat(1u);
x_609 = lean_nat_sub(x_605, x_608);
lean_dec(x_605);
x_610 = lean_unbox(x_599);
lean_dec(x_599);
x_611 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_589, x_598, x_610, x_600, x_603, x_607, x_609, x_8, x_604);
return x_611;
}
else
{
uint8_t x_612; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_589);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_602);
if (x_612 == 0)
{
return x_602;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_602, 0);
x_614 = lean_ctor_get(x_602, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_602);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_589);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_616 = l_Lean_Name_toString___closed__1;
x_617 = l_Lean_Name_toStringWithSep___main(x_616, x_2);
x_618 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_618, 0, x_617);
x_619 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_619, 0, x_618);
x_620 = l___private_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_621 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_619);
x_622 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3;
x_623 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_alloc_ctor(22, 1, 0);
lean_ctor_set(x_624, 0, x_623);
if (lean_is_scalar(x_596)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_596;
 lean_ctor_set_tag(x_625, 1);
}
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_595);
return x_625;
}
}
}
else
{
uint8_t x_632; 
lean_dec(x_589);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_632 = !lean_is_exclusive(x_592);
if (x_632 == 0)
{
return x_592;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_592, 0);
x_634 = lean_ctor_get(x_592, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_592);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
else
{
uint8_t x_636; 
lean_dec(x_589);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_636 = !lean_is_exclusive(x_590);
if (x_636 == 0)
{
return x_590;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_590, 0);
x_638 = lean_ctor_get(x_590, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_590);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
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
x_14 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_13, x_6, x_7);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_1, x_3);
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
lean_object* _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1() {
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
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_9 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
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
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_42 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
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
x_18 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
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
x_27 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_3, x_19, x_17, x_2, x_2);
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
x_30 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_3, x_29, x_28, x_2, x_2);
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
x_37 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_3, x_33, x_31, x_2, x_2);
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
x_40 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_3, x_39, x_38, x_2, x_2);
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
x_8 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_6, x_2, x_5);
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
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object* x_1, lean_object* x_2) {
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
x_20 = lean_io_ref_get(x_13, x_16);
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
x_25 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_io_ref_set(x_13, x_24, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_19);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_19);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
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
lean_dec(x_24);
lean_dec(x_19);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
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
else
{
uint8_t x_44; 
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_3);
if (x_48 == 0)
{
return x_3;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_3, 0);
x_50 = lean_ctor_get(x_3, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_3);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(x_1, x_6, x_6, x_8, x_9);
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
x_19 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(x_18, x_7);
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
x_23 = lean_io_ref_get(x_3, x_21);
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
x_28 = lean_io_ref_reset(x_3, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_io_ref_set(x_3, x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_22);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_22);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_27);
lean_dec(x_22);
x_39 = !lean_is_exclusive(x_28);
if (x_39 == 0)
{
return x_28;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
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
lean_dec(x_22);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Lean_Name_toString___closed__1;
x_53 = l_Lean_Name_toStringWithSep___main(x_52, x_51);
x_54 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_55 = lean_string_append(x_54, x_53);
lean_dec(x_53);
x_56 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_57 = lean_string_append(x_55, x_56);
x_58 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_58);
return x_4;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_array_get_size(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(x_1, x_59, x_59, x_61, x_62);
lean_dec(x_61);
lean_dec(x_59);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 4);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 5);
lean_inc(x_69);
lean_dec(x_1);
x_70 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_71 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_71, 0, x_65);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(x_71, x_60);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_64);
lean_ctor_set(x_75, 2, x_66);
lean_ctor_set(x_75, 3, x_67);
lean_ctor_set(x_75, 4, x_68);
lean_ctor_set(x_75, 5, x_69);
x_76 = lean_io_ref_get(x_3, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_75);
x_79 = x_75;
x_80 = lean_array_push(x_77, x_79);
x_81 = lean_io_ref_reset(x_3, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_io_ref_set(x_3, x_80, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_75);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_89 = x_83;
} else {
 lean_dec_ref(x_83);
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_80);
lean_dec(x_75);
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
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
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_75);
x_95 = lean_ctor_get(x_76, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_97 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_99 = lean_ctor_get(x_72, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_72, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_101 = x_72;
} else {
 lean_dec_ref(x_72);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_1, 0);
lean_inc(x_103);
lean_dec(x_1);
x_104 = l_Lean_Name_toString___closed__1;
x_105 = l_Lean_Name_toStringWithSep___main(x_104, x_103);
x_106 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
x_107 = lean_string_append(x_106, x_105);
lean_dec(x_105);
x_108 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_109 = lean_string_append(x_107, x_108);
x_110 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_60);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_4);
if (x_112 == 0)
{
return x_4;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_4, 0);
x_114 = lean_ctor_get(x_4, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_4);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_2, x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_3, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
lean_object* _init_l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_Lean_registerParametricAttribute___rarg___closed__1;
x_8 = l_Lean_registerParametricAttribute___rarg___closed__2;
x_9 = l_Lean_registerParametricAttribute___rarg___closed__3;
x_10 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1;
x_11 = l_Lean_registerParametricAttribute___rarg___closed__4;
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_9);
lean_ctor_set(x_12, 4, x_10);
lean_ctor_set(x_12, 5, x_11);
x_13 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__5(x_12, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___rarg___lambda__5___boxed), 9, 4);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_4);
x_17 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_5);
lean_inc(x_17);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
x_19 = l_Lean_registerBuiltinAttribute(x_17, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_18);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore), 4, 2);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_4);
x_6 = lean_unsigned_to_nat(10000u);
lean_inc(x_1);
x_7 = l_Lean_Meta_run___rarg(x_1, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = l_Lean_Meta_Exception_toStr(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Meta_Exception_toStr(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
lean_object* x_16; 
lean_dec(x_7);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
return x_16;
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
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorAttr___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkRecursorAttr___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_mkRecursorAttr___lambda__2), 3, 0);
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
x_7 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1(x_2, x_3, x_4, x_5, x_6, x_1);
return x_7;
}
}
lean_object* l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_mkRecursorAttr___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
x_10 = l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
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
l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__4);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__3);
l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__4);
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
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__22);
l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23 = _init_l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__23);
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
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__2);
l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3 = _init_l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__3);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3);
l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4);
l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1 = _init_l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1);
l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1 = _init_l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1();
lean_mark_persistent(l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1);
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
