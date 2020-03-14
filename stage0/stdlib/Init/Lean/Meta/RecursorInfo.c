// Lean compiler output
// Module: Init.Lean.Meta.RecursorInfo
// Imports: Init.Data.Nat.Control Init.Lean.AuxRecursor Init.Lean.Util.FindExpr Init.Lean.Meta.ExprDefEq Init.Lean.Meta.Message
#include "runtime/lean.h"
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
lean_object* l_Lean_Meta_recursorAttribute;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_brecOnSuffix___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Option_HasRepr___rarg___closed__2;
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
lean_object* l_Lean_Meta_mkRecursorAttr(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
lean_object* l_Array_getIdx_x3f___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_List_repr___rarg___closed__1;
extern lean_object* l_Option_HasRepr___rarg___closed__1;
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__5(lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__4___closed__1;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__4;
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object*);
lean_object* l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
extern lean_object* l_Lean_registerTagAttribute___closed__1;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__14;
lean_object* l_Lean_Meta_recOnSuffix;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__5;
lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_object* l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__5;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
lean_object* l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_auxRecExt;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__3;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___closed__2;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__2;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__6;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__8;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__4;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_List_replicate___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix;
lean_object* l_Array_back___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
lean_object* l_Array_binSearchAux___main___at_Lean_Meta_getMajorPos_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__13;
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_Meta_brecOnSuffix;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6(uint8_t, lean_object*);
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8(uint8_t, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
extern lean_object* l_Lean_numLitKind;
lean_object* l_EStateM_bind___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__1;
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1;
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2(uint8_t, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_List_lengthAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__2;
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Meta_run___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__7___boxed(lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
extern lean_object* l_IO_println___rarg___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_HasToString(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___closed__1;
lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__8___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
lean_object* l_Lean_Meta_mkRecOnFor(lean_object*);
extern lean_object* l_Lean_mkRecFor___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__1;
lean_object* l_Lean_Meta_RecursorUnivLevelPos_hasToString___closed__1;
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__2;
extern lean_object* l___private_Init_Lean_Environment_5__envExtensionsRef;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__9;
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__3(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMajorPos_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Meta_mkBRecOnFor(lean_object*);
lean_object* l_Lean_RecursorVal_getInduct(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_casesOnSuffix___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
extern lean_object* l_Option_HasRepr___rarg___closed__3;
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__11;
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_HasToString___spec__1(lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
extern lean_object* l_PersistentArray_Stats_toString___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4;
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__12;
lean_object* lean_io_ref_reset(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCasesOnFor(lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___closed__1;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_getIdx_x3f___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qsortAux___main___at_Lean_Meta_mkRecursorAttr___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__16;
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__4(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Exception_toStr(lean_object*);
extern lean_object* l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* lean_io_initializing(lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__10;
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_ParametricAttribute_Inhabited___closed__1;
lean_object* l_Lean_ParametricAttribute_getParam___at_Lean_Meta_getMajorPos_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Nat_Inhabited;
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_RecursorInfo_HasToString___spec__2___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_QSort_1__partitionAux___main___at_Lean_Meta_mkRecursorAttr___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___boxed(lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__15;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_RecursorInfo_HasToString___closed__3;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
lean_object* l_Lean_Meta_mkRecursorAttr___closed__2;
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object**);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_recOnSuffix___closed__1;
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1(lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object*, lean_object*, lean_object*);
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
x_7 = l_IO_println___rarg___closed__1;
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
x_85 = l_PersistentArray_Stats_toString___closed__4;
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
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_5);
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
x_11 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_5);
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
x_11 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_6);
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
x_12 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed builtin recursor");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1;
x_2 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_16 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_15);
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
x_27 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_26);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_28);
x_29 = l_List_range(x_28);
x_30 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_25, x_29);
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
x_50 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__1(x_49);
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
x_61 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__2(x_60);
x_62 = lean_ctor_get(x_2, 3);
lean_inc(x_62);
lean_inc(x_62);
x_63 = l_List_range(x_62);
x_64 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_59, x_63);
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
x_81 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
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
x_83 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2;
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
lean_object* l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected recursor information");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1;
x_2 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_48 = l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
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
x_50 = l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2;
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
lean_object* l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid user defined recursor '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', result type must be of the form (C t), ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("where C is a bound variable, and t is a (possibly empty) sequence of bound variables");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Lean_Expr_isFVar(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Name_toStringWithSep___main(x_7, x_1);
x_9 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_array_get_size(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_3, x_3, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = l_Lean_Name_toString___closed__1;
x_23 = l_Lean_Name_toStringWithSep___main(x_22, x_1);
x_24 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3;
x_29 = lean_string_append(x_27, x_28);
x_30 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Array_getIdx_x3f___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_2, x_1, x_3);
return x_4;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ill-formed recursor '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid user defined recursor, '");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' does not support dependent elimination, ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("and position of the major premise was not specified ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid major premise position for user defined recursor, recursor has only ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" arguments");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Array_back___at___private_Init_Lean_Meta_ExprDefEq_14__processAssignmentFOApproxAux___spec__1(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_9, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_1);
x_14 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Char_HasRepr___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_7);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = l_Lean_Name_toString___closed__1;
x_27 = l_Lean_Name_toStringWithSep___main(x_26, x_1);
x_28 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3;
x_31 = lean_string_append(x_29, x_30);
x_32 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4;
x_33 = lean_string_append(x_31, x_32);
x_34 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_array_get_size(x_3);
x_40 = lean_nat_dec_lt(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = l_Nat_repr(x_39);
x_42 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
return x_47;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
x_48 = lean_array_fget(x_3, x_38);
x_49 = l_Array_contains___at_Lean_Meta_CheckAssignment_check___main___spec__2(x_5, x_48);
x_50 = lean_box(x_49);
lean_inc(x_38);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
return x_53;
}
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_getIdx_x3f___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_getIdx_x3f___at___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor parameter");
return x_1;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_16, x_3, x_9, x_7, x_8);
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_1);
x_29 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; 
lean_free_object(x_21);
x_34 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_34;
x_8 = x_24;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = l_Lean_LocalDecl_binderInfo(x_36);
lean_dec(x_36);
x_39 = l_Lean_BinderInfo_isInstImplicit(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_40 = l_Lean_Name_toString___closed__1;
x_41 = l_Lean_Name_toStringWithSep___main(x_40, x_1);
x_42 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_37);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_48;
x_8 = x_37;
goto _start;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_dec(x_17);
x_55 = lean_array_push(x_6, x_18);
x_5 = x_12;
x_6 = x_55;
x_8 = x_54;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_6);
lean_ctor_set(x_61, 1, x_8);
return x_61;
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Array_empty___closed__1;
lean_inc(x_3);
x_8 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_4, x_3, x_3, x_7, x_5, x_6);
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
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* _init_l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , type of the major premise does not contain the recursor index");
return x_1;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_21 = l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_20, x_5, x_11, x_9, x_10);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = l_Lean_Name_toString___closed__1;
x_26 = l_Lean_Name_toStringWithSep___main(x_25, x_1);
x_27 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
x_30 = lean_string_append(x_28, x_29);
x_31 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Name_toString___closed__1;
x_34 = l_Lean_Name_toStringWithSep___main(x_33, x_1);
x_35 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_36 = lean_string_append(x_35, x_34);
lean_dec(x_34);
x_37 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1;
x_38 = lean_string_append(x_36, x_37);
x_39 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_32);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_ctor_get(x_22, 0);
lean_inc(x_42);
lean_dec(x_22);
x_43 = lean_array_push(x_8, x_42);
x_7 = x_14;
x_8 = x_43;
x_10 = x_41;
goto _start;
}
}
else
{
uint8_t x_45; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_8);
lean_ctor_set(x_49, 1, x_10);
return x_49;
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Array_empty___closed__1;
lean_inc(x_4);
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_4, x_4, x_8, x_6, x_7);
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
lean_object* l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_findIdxMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , motive result sort must be Prop or (Sort u) where u is a universe level parameter");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; 
lean_dec(x_1);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
return x_16;
}
case 4:
{
lean_object* x_17; 
lean_dec(x_1);
lean_inc(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
default: 
{
lean_object* x_18; 
x_18 = lean_box(0);
x_5 = x_18;
goto block_14;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_5 = x_19;
goto block_14;
}
block_14:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_1);
x_8 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' , major premise type does not contain universe level parameter '");
return x_1;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_11, x_3, x_13);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_4);
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_1);
x_17 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1;
x_20 = lean_string_append(x_18, x_19);
x_21 = l_Lean_Name_toStringWithSep___main(x_15, x_9);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_array_push(x_4, x_28);
x_4 = x_29;
x_5 = x_10;
goto _start;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_9);
x_31 = lean_box(0);
x_32 = lean_array_push(x_4, x_31);
x_4 = x_32;
x_5 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_List_redLength___main___rarg(x_4);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
x_9 = l_List_toArrayAux___main___rarg(x_4, x_8);
x_10 = l_Array_empty___closed__1;
x_11 = l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_3, x_9, x_10, x_2, x_5, x_6);
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
lean_object* l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_8, x_6);
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
x_26 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_24, x_6);
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
x_42 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_40, x_6);
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
x_59 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_56, x_6);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_57, x_61);
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
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_19 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_17, x_15, x_18);
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
x_30 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_28, x_26, x_29);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_21 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_4, x_4, x_19, x_20, x_8, x_9);
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
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_3, x_4, x_5, x_11, x_13, x_6, x_7);
return x_14;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_25 = lean_alloc_closure((void*)(l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed), 7, 3);
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
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1() {
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
lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1;
lean_inc(x_8);
x_10 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_8, x_8, x_9, x_6, x_7);
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
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_FindImpl_findM_x3f___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__1(x_1, x_5, x_3, x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', motive must have a type of the form ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), ");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(i : B A) is a (possibly empty) telescope (aka indices), and I is a constant");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isSort(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_8 = l_Lean_Name_toString___closed__1;
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_1);
x_10 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_11 = lean_string_append(x_10, x_9);
lean_dec(x_9);
x_12 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_array_get_size(x_2);
x_21 = lean_array_get_size(x_4);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_1);
x_25 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2;
x_30 = lean_string_append(x_28, x_29);
x_31 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3;
x_32 = lean_string_append(x_30, x_31);
x_33 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_1);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_1);
x_18 = l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType(x_1, x_2, x_15, x_14, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_1);
x_20 = l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel(x_1, x_15, x_16, x_19);
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
x_24 = l___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos(x_1, x_23, x_21, x_4, x_16, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive(x_5, x_6, x_7, x_8, x_9, x_16, x_26);
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
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', type of the major premise must be of the form (I ...), where I is a constant");
return x_1;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_17 = l___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos(x_2, x_3, x_6, x_11, x_13, x_14);
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
x_20 = l___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos(x_2, x_3, x_7, x_9, x_11, x_13, x_19);
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
x_27 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed), 17, 13);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
x_49 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1;
x_52 = lean_string_append(x_50, x_51);
x_53 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_14);
return x_54;
}
}
}
}
lean_object* _init_l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', indices must occur before major premise");
return x_1;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_7);
lean_inc(x_2);
x_10 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_12);
lean_inc(x_2);
x_14 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_47; 
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
x_47 = lean_unbox(x_21);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_array_get_size(x_6);
x_22 = x_48;
goto block_46;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_array_get_size(x_6);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_sub(x_49, x_50);
lean_dec(x_49);
x_22 = x_51;
goto block_46;
}
block_46:
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
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_25, x_12);
x_28 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_27);
x_29 = lean_mk_array(x_27, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_27, x_30);
lean_dec(x_27);
x_32 = lean_unbox(x_21);
lean_dec(x_21);
x_33 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_13, x_20, x_32, x_22, x_25, x_29, x_31, x_8, x_26);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_13);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_38 = l_Lean_Name_toString___closed__1;
x_39 = l_Lean_Name_toStringWithSep___main(x_38, x_2);
x_40 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_41 = lean_string_append(x_40, x_39);
lean_dec(x_39);
x_42 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_43 = lean_string_append(x_41, x_42);
x_44 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_18)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_18;
 lean_ctor_set_tag(x_45, 1);
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_17);
return x_45;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_14);
if (x_52 == 0)
{
return x_14;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_14, 0);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_14);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_10);
if (x_56 == 0)
{
return x_10;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_10, 0);
x_58 = lean_ctor_get(x_10, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_10);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
case 1:
{
lean_object* x_60; 
lean_dec(x_7);
lean_inc(x_2);
x_60 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_62);
lean_inc(x_2);
x_64 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_97; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_68 = x_64;
} else {
 lean_dec_ref(x_64);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_97 = lean_unbox(x_71);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = lean_array_get_size(x_6);
x_72 = x_98;
goto block_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_array_get_size(x_6);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_99, x_100);
lean_dec(x_99);
x_72 = x_101;
goto block_96;
}
block_96:
{
uint8_t x_73; 
x_73 = lean_nat_dec_lt(x_70, x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_68);
lean_inc(x_8);
x_74 = l_Lean_Meta_inferType(x_69, x_8, x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Expr_getAppNumArgsAux___main(x_75, x_62);
x_78 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_77);
x_79 = lean_mk_array(x_77, x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_77, x_80);
lean_dec(x_77);
x_82 = lean_unbox(x_71);
lean_dec(x_71);
x_83 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_63, x_70, x_82, x_72, x_75, x_79, x_81, x_8, x_76);
return x_83;
}
else
{
uint8_t x_84; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_74);
if (x_84 == 0)
{
return x_74;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_74, 0);
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_74);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_88 = l_Lean_Name_toString___closed__1;
x_89 = l_Lean_Name_toStringWithSep___main(x_88, x_2);
x_90 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_91 = lean_string_append(x_90, x_89);
lean_dec(x_89);
x_92 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_93 = lean_string_append(x_91, x_92);
x_94 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_94, 0, x_93);
if (lean_is_scalar(x_68)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_68;
 lean_ctor_set_tag(x_95, 1);
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_67);
return x_95;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_64);
if (x_102 == 0)
{
return x_64;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_64, 0);
x_104 = lean_ctor_get(x_64, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_64);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_60);
if (x_106 == 0)
{
return x_60;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_60, 0);
x_108 = lean_ctor_get(x_60, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_60);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
case 2:
{
lean_object* x_110; 
lean_dec(x_7);
lean_inc(x_2);
x_110 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_unsigned_to_nat(0u);
x_113 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_112);
lean_inc(x_2);
x_114 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_111);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_147; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
lean_dec(x_115);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_147 = lean_unbox(x_121);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_array_get_size(x_6);
x_122 = x_148;
goto block_146;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_array_get_size(x_6);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_nat_sub(x_149, x_150);
lean_dec(x_149);
x_122 = x_151;
goto block_146;
}
block_146:
{
uint8_t x_123; 
x_123 = lean_nat_dec_lt(x_120, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_118);
lean_inc(x_8);
x_124 = l_Lean_Meta_inferType(x_119, x_8, x_117);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Expr_getAppNumArgsAux___main(x_125, x_112);
x_128 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_127);
x_129 = lean_mk_array(x_127, x_128);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_sub(x_127, x_130);
lean_dec(x_127);
x_132 = lean_unbox(x_121);
lean_dec(x_121);
x_133 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_113, x_120, x_132, x_122, x_125, x_129, x_131, x_8, x_126);
return x_133;
}
else
{
uint8_t x_134; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_124);
if (x_134 == 0)
{
return x_124;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_124, 0);
x_136 = lean_ctor_get(x_124, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_124);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_138 = l_Lean_Name_toString___closed__1;
x_139 = l_Lean_Name_toStringWithSep___main(x_138, x_2);
x_140 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_141 = lean_string_append(x_140, x_139);
lean_dec(x_139);
x_142 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_143 = lean_string_append(x_141, x_142);
x_144 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_144, 0, x_143);
if (lean_is_scalar(x_118)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_118;
 lean_ctor_set_tag(x_145, 1);
}
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_117);
return x_145;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_113);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_114);
if (x_152 == 0)
{
return x_114;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_114, 0);
x_154 = lean_ctor_get(x_114, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_114);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_110);
if (x_156 == 0)
{
return x_110;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_110, 0);
x_158 = lean_ctor_get(x_110, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_110);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
case 3:
{
lean_object* x_160; 
lean_dec(x_7);
lean_inc(x_2);
x_160 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_162);
lean_inc(x_2);
x_164 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_197; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_165, 0);
lean_inc(x_169);
lean_dec(x_165);
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_197 = lean_unbox(x_171);
if (x_197 == 0)
{
lean_object* x_198; 
x_198 = lean_array_get_size(x_6);
x_172 = x_198;
goto block_196;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_array_get_size(x_6);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_sub(x_199, x_200);
lean_dec(x_199);
x_172 = x_201;
goto block_196;
}
block_196:
{
uint8_t x_173; 
x_173 = lean_nat_dec_lt(x_170, x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_168);
lean_inc(x_8);
x_174 = l_Lean_Meta_inferType(x_169, x_8, x_167);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Expr_getAppNumArgsAux___main(x_175, x_162);
x_178 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_177);
x_179 = lean_mk_array(x_177, x_178);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_nat_sub(x_177, x_180);
lean_dec(x_177);
x_182 = lean_unbox(x_171);
lean_dec(x_171);
x_183 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_163, x_170, x_182, x_172, x_175, x_179, x_181, x_8, x_176);
return x_183;
}
else
{
uint8_t x_184; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_174);
if (x_184 == 0)
{
return x_174;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_174, 0);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_174);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_188 = l_Lean_Name_toString___closed__1;
x_189 = l_Lean_Name_toStringWithSep___main(x_188, x_2);
x_190 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_191 = lean_string_append(x_190, x_189);
lean_dec(x_189);
x_192 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_193 = lean_string_append(x_191, x_192);
x_194 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_is_scalar(x_168)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_168;
 lean_ctor_set_tag(x_195, 1);
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_167);
return x_195;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_163);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_164);
if (x_202 == 0)
{
return x_164;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_164, 0);
x_204 = lean_ctor_get(x_164, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_164);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_160);
if (x_206 == 0)
{
return x_160;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_160, 0);
x_208 = lean_ctor_get(x_160, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_160);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
case 4:
{
lean_object* x_210; 
lean_dec(x_7);
lean_inc(x_2);
x_210 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_unsigned_to_nat(0u);
x_213 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_212);
lean_inc(x_2);
x_214 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_211);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_247; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_218 = x_214;
} else {
 lean_dec_ref(x_214);
 x_218 = lean_box(0);
}
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
lean_dec(x_215);
x_220 = lean_ctor_get(x_216, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 1);
lean_inc(x_221);
lean_dec(x_216);
x_247 = lean_unbox(x_221);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_array_get_size(x_6);
x_222 = x_248;
goto block_246;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_array_get_size(x_6);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_nat_sub(x_249, x_250);
lean_dec(x_249);
x_222 = x_251;
goto block_246;
}
block_246:
{
uint8_t x_223; 
x_223 = lean_nat_dec_lt(x_220, x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec(x_218);
lean_inc(x_8);
x_224 = l_Lean_Meta_inferType(x_219, x_8, x_217);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_Expr_getAppNumArgsAux___main(x_225, x_212);
x_228 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_227);
x_229 = lean_mk_array(x_227, x_228);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_sub(x_227, x_230);
lean_dec(x_227);
x_232 = lean_unbox(x_221);
lean_dec(x_221);
x_233 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_213, x_220, x_232, x_222, x_225, x_229, x_231, x_8, x_226);
return x_233;
}
else
{
uint8_t x_234; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_213);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_224);
if (x_234 == 0)
{
return x_224;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_224, 0);
x_236 = lean_ctor_get(x_224, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_224);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_213);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_238 = l_Lean_Name_toString___closed__1;
x_239 = l_Lean_Name_toStringWithSep___main(x_238, x_2);
x_240 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_241 = lean_string_append(x_240, x_239);
lean_dec(x_239);
x_242 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_243 = lean_string_append(x_241, x_242);
x_244 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_244, 0, x_243);
if (lean_is_scalar(x_218)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_218;
 lean_ctor_set_tag(x_245, 1);
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_217);
return x_245;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_213);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_252 = !lean_is_exclusive(x_214);
if (x_252 == 0)
{
return x_214;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_214, 0);
x_254 = lean_ctor_get(x_214, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_214);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_210);
if (x_256 == 0)
{
return x_210;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_210, 0);
x_258 = lean_ctor_get(x_210, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_210);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
case 5:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_ctor_get(x_5, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_5, 1);
lean_inc(x_261);
lean_dec(x_5);
x_262 = lean_array_set(x_6, x_7, x_261);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_nat_sub(x_7, x_263);
lean_dec(x_7);
x_5 = x_260;
x_6 = x_262;
x_7 = x_264;
goto _start;
}
case 6:
{
lean_object* x_266; 
lean_dec(x_7);
lean_inc(x_2);
x_266 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = lean_unsigned_to_nat(0u);
x_269 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_268);
lean_inc(x_2);
x_270 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_267);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_303; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_274 = x_270;
} else {
 lean_dec_ref(x_270);
 x_274 = lean_box(0);
}
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec(x_271);
x_276 = lean_ctor_get(x_272, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 1);
lean_inc(x_277);
lean_dec(x_272);
x_303 = lean_unbox(x_277);
if (x_303 == 0)
{
lean_object* x_304; 
x_304 = lean_array_get_size(x_6);
x_278 = x_304;
goto block_302;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_array_get_size(x_6);
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_nat_sub(x_305, x_306);
lean_dec(x_305);
x_278 = x_307;
goto block_302;
}
block_302:
{
uint8_t x_279; 
x_279 = lean_nat_dec_lt(x_276, x_278);
if (x_279 == 0)
{
lean_object* x_280; 
lean_dec(x_274);
lean_inc(x_8);
x_280 = l_Lean_Meta_inferType(x_275, x_8, x_273);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = l_Lean_Expr_getAppNumArgsAux___main(x_281, x_268);
x_284 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_283);
x_285 = lean_mk_array(x_283, x_284);
x_286 = lean_unsigned_to_nat(1u);
x_287 = lean_nat_sub(x_283, x_286);
lean_dec(x_283);
x_288 = lean_unbox(x_277);
lean_dec(x_277);
x_289 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_269, x_276, x_288, x_278, x_281, x_285, x_287, x_8, x_282);
return x_289;
}
else
{
uint8_t x_290; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_269);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_290 = !lean_is_exclusive(x_280);
if (x_290 == 0)
{
return x_280;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_280, 0);
x_292 = lean_ctor_get(x_280, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_280);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_269);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_294 = l_Lean_Name_toString___closed__1;
x_295 = l_Lean_Name_toStringWithSep___main(x_294, x_2);
x_296 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_297 = lean_string_append(x_296, x_295);
lean_dec(x_295);
x_298 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_299 = lean_string_append(x_297, x_298);
x_300 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_300, 0, x_299);
if (lean_is_scalar(x_274)) {
 x_301 = lean_alloc_ctor(1, 2, 0);
} else {
 x_301 = x_274;
 lean_ctor_set_tag(x_301, 1);
}
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_273);
return x_301;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_269);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_270);
if (x_308 == 0)
{
return x_270;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_270, 0);
x_310 = lean_ctor_get(x_270, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_270);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_266);
if (x_312 == 0)
{
return x_266;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_266, 0);
x_314 = lean_ctor_get(x_266, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_266);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
case 7:
{
lean_object* x_316; 
lean_dec(x_7);
lean_inc(x_2);
x_316 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_unsigned_to_nat(0u);
x_319 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_318);
lean_inc(x_2);
x_320 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_317);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_353; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_324 = x_320;
} else {
 lean_dec_ref(x_320);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
lean_dec(x_321);
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_dec(x_322);
x_353 = lean_unbox(x_327);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = lean_array_get_size(x_6);
x_328 = x_354;
goto block_352;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_array_get_size(x_6);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_sub(x_355, x_356);
lean_dec(x_355);
x_328 = x_357;
goto block_352;
}
block_352:
{
uint8_t x_329; 
x_329 = lean_nat_dec_lt(x_326, x_328);
if (x_329 == 0)
{
lean_object* x_330; 
lean_dec(x_324);
lean_inc(x_8);
x_330 = l_Lean_Meta_inferType(x_325, x_8, x_323);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = l_Lean_Expr_getAppNumArgsAux___main(x_331, x_318);
x_334 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_333);
x_335 = lean_mk_array(x_333, x_334);
x_336 = lean_unsigned_to_nat(1u);
x_337 = lean_nat_sub(x_333, x_336);
lean_dec(x_333);
x_338 = lean_unbox(x_327);
lean_dec(x_327);
x_339 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_319, x_326, x_338, x_328, x_331, x_335, x_337, x_8, x_332);
return x_339;
}
else
{
uint8_t x_340; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_319);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_340 = !lean_is_exclusive(x_330);
if (x_340 == 0)
{
return x_330;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_330, 0);
x_342 = lean_ctor_get(x_330, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_330);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_319);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_344 = l_Lean_Name_toString___closed__1;
x_345 = l_Lean_Name_toStringWithSep___main(x_344, x_2);
x_346 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_347 = lean_string_append(x_346, x_345);
lean_dec(x_345);
x_348 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_349 = lean_string_append(x_347, x_348);
x_350 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_350, 0, x_349);
if (lean_is_scalar(x_324)) {
 x_351 = lean_alloc_ctor(1, 2, 0);
} else {
 x_351 = x_324;
 lean_ctor_set_tag(x_351, 1);
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_323);
return x_351;
}
}
}
else
{
uint8_t x_358; 
lean_dec(x_319);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_358 = !lean_is_exclusive(x_320);
if (x_358 == 0)
{
return x_320;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_320, 0);
x_360 = lean_ctor_get(x_320, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_320);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_362 = !lean_is_exclusive(x_316);
if (x_362 == 0)
{
return x_316;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_316, 0);
x_364 = lean_ctor_get(x_316, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_316);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
case 8:
{
lean_object* x_366; 
lean_dec(x_7);
lean_inc(x_2);
x_366 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_unsigned_to_nat(0u);
x_369 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_368);
lean_inc(x_2);
x_370 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_367);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_403; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_374 = x_370;
} else {
 lean_dec_ref(x_370);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
lean_dec(x_371);
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_372, 1);
lean_inc(x_377);
lean_dec(x_372);
x_403 = lean_unbox(x_377);
if (x_403 == 0)
{
lean_object* x_404; 
x_404 = lean_array_get_size(x_6);
x_378 = x_404;
goto block_402;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_array_get_size(x_6);
x_406 = lean_unsigned_to_nat(1u);
x_407 = lean_nat_sub(x_405, x_406);
lean_dec(x_405);
x_378 = x_407;
goto block_402;
}
block_402:
{
uint8_t x_379; 
x_379 = lean_nat_dec_lt(x_376, x_378);
if (x_379 == 0)
{
lean_object* x_380; 
lean_dec(x_374);
lean_inc(x_8);
x_380 = l_Lean_Meta_inferType(x_375, x_8, x_373);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lean_Expr_getAppNumArgsAux___main(x_381, x_368);
x_384 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_383);
x_385 = lean_mk_array(x_383, x_384);
x_386 = lean_unsigned_to_nat(1u);
x_387 = lean_nat_sub(x_383, x_386);
lean_dec(x_383);
x_388 = lean_unbox(x_377);
lean_dec(x_377);
x_389 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_369, x_376, x_388, x_378, x_381, x_385, x_387, x_8, x_382);
return x_389;
}
else
{
uint8_t x_390; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_369);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_390 = !lean_is_exclusive(x_380);
if (x_390 == 0)
{
return x_380;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_380, 0);
x_392 = lean_ctor_get(x_380, 1);
lean_inc(x_392);
lean_inc(x_391);
lean_dec(x_380);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_378);
lean_dec(x_377);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_369);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_394 = l_Lean_Name_toString___closed__1;
x_395 = l_Lean_Name_toStringWithSep___main(x_394, x_2);
x_396 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_397 = lean_string_append(x_396, x_395);
lean_dec(x_395);
x_398 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_399 = lean_string_append(x_397, x_398);
x_400 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_400, 0, x_399);
if (lean_is_scalar(x_374)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_374;
 lean_ctor_set_tag(x_401, 1);
}
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_373);
return x_401;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_369);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_408 = !lean_is_exclusive(x_370);
if (x_408 == 0)
{
return x_370;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_370, 0);
x_410 = lean_ctor_get(x_370, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_370);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_412 = !lean_is_exclusive(x_366);
if (x_412 == 0)
{
return x_366;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_366, 0);
x_414 = lean_ctor_get(x_366, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_366);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
return x_415;
}
}
}
case 9:
{
lean_object* x_416; 
lean_dec(x_7);
lean_inc(x_2);
x_416 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
x_418 = lean_unsigned_to_nat(0u);
x_419 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_418);
lean_inc(x_2);
x_420 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_417);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_453; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_424 = x_420;
} else {
 lean_dec_ref(x_420);
 x_424 = lean_box(0);
}
x_425 = lean_ctor_get(x_421, 0);
lean_inc(x_425);
lean_dec(x_421);
x_426 = lean_ctor_get(x_422, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_422, 1);
lean_inc(x_427);
lean_dec(x_422);
x_453 = lean_unbox(x_427);
if (x_453 == 0)
{
lean_object* x_454; 
x_454 = lean_array_get_size(x_6);
x_428 = x_454;
goto block_452;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_array_get_size(x_6);
x_456 = lean_unsigned_to_nat(1u);
x_457 = lean_nat_sub(x_455, x_456);
lean_dec(x_455);
x_428 = x_457;
goto block_452;
}
block_452:
{
uint8_t x_429; 
x_429 = lean_nat_dec_lt(x_426, x_428);
if (x_429 == 0)
{
lean_object* x_430; 
lean_dec(x_424);
lean_inc(x_8);
x_430 = l_Lean_Meta_inferType(x_425, x_8, x_423);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = l_Lean_Expr_getAppNumArgsAux___main(x_431, x_418);
x_434 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_433);
x_435 = lean_mk_array(x_433, x_434);
x_436 = lean_unsigned_to_nat(1u);
x_437 = lean_nat_sub(x_433, x_436);
lean_dec(x_433);
x_438 = lean_unbox(x_427);
lean_dec(x_427);
x_439 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_419, x_426, x_438, x_428, x_431, x_435, x_437, x_8, x_432);
return x_439;
}
else
{
uint8_t x_440; 
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_419);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_430);
if (x_440 == 0)
{
return x_430;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_430, 0);
x_442 = lean_ctor_get(x_430, 1);
lean_inc(x_442);
lean_inc(x_441);
lean_dec(x_430);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
return x_443;
}
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_426);
lean_dec(x_425);
lean_dec(x_419);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_444 = l_Lean_Name_toString___closed__1;
x_445 = l_Lean_Name_toStringWithSep___main(x_444, x_2);
x_446 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_447 = lean_string_append(x_446, x_445);
lean_dec(x_445);
x_448 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_449 = lean_string_append(x_447, x_448);
x_450 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_450, 0, x_449);
if (lean_is_scalar(x_424)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_424;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_423);
return x_451;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_419);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_458 = !lean_is_exclusive(x_420);
if (x_458 == 0)
{
return x_420;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_420, 0);
x_460 = lean_ctor_get(x_420, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_420);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_462 = !lean_is_exclusive(x_416);
if (x_462 == 0)
{
return x_416;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_416, 0);
x_464 = lean_ctor_get(x_416, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_416);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
case 10:
{
lean_object* x_466; 
lean_dec(x_7);
lean_inc(x_2);
x_466 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_468 = lean_unsigned_to_nat(0u);
x_469 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_468);
lean_inc(x_2);
x_470 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_467);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; uint8_t x_503; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_470, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_474 = x_470;
} else {
 lean_dec_ref(x_470);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_471, 0);
lean_inc(x_475);
lean_dec(x_471);
x_476 = lean_ctor_get(x_472, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_472, 1);
lean_inc(x_477);
lean_dec(x_472);
x_503 = lean_unbox(x_477);
if (x_503 == 0)
{
lean_object* x_504; 
x_504 = lean_array_get_size(x_6);
x_478 = x_504;
goto block_502;
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_505 = lean_array_get_size(x_6);
x_506 = lean_unsigned_to_nat(1u);
x_507 = lean_nat_sub(x_505, x_506);
lean_dec(x_505);
x_478 = x_507;
goto block_502;
}
block_502:
{
uint8_t x_479; 
x_479 = lean_nat_dec_lt(x_476, x_478);
if (x_479 == 0)
{
lean_object* x_480; 
lean_dec(x_474);
lean_inc(x_8);
x_480 = l_Lean_Meta_inferType(x_475, x_8, x_473);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; uint8_t x_488; lean_object* x_489; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = l_Lean_Expr_getAppNumArgsAux___main(x_481, x_468);
x_484 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_483);
x_485 = lean_mk_array(x_483, x_484);
x_486 = lean_unsigned_to_nat(1u);
x_487 = lean_nat_sub(x_483, x_486);
lean_dec(x_483);
x_488 = lean_unbox(x_477);
lean_dec(x_477);
x_489 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_469, x_476, x_488, x_478, x_481, x_485, x_487, x_8, x_482);
return x_489;
}
else
{
uint8_t x_490; 
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_469);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_490 = !lean_is_exclusive(x_480);
if (x_490 == 0)
{
return x_480;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_480, 0);
x_492 = lean_ctor_get(x_480, 1);
lean_inc(x_492);
lean_inc(x_491);
lean_dec(x_480);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_469);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_494 = l_Lean_Name_toString___closed__1;
x_495 = l_Lean_Name_toStringWithSep___main(x_494, x_2);
x_496 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_497 = lean_string_append(x_496, x_495);
lean_dec(x_495);
x_498 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_499 = lean_string_append(x_497, x_498);
x_500 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_500, 0, x_499);
if (lean_is_scalar(x_474)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_474;
 lean_ctor_set_tag(x_501, 1);
}
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_473);
return x_501;
}
}
}
else
{
uint8_t x_508; 
lean_dec(x_469);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_508 = !lean_is_exclusive(x_470);
if (x_508 == 0)
{
return x_470;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_470, 0);
x_510 = lean_ctor_get(x_470, 1);
lean_inc(x_510);
lean_inc(x_509);
lean_dec(x_470);
x_511 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
return x_511;
}
}
}
else
{
uint8_t x_512; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_512 = !lean_is_exclusive(x_466);
if (x_512 == 0)
{
return x_466;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_466, 0);
x_514 = lean_ctor_get(x_466, 1);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_466);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
return x_515;
}
}
}
case 11:
{
lean_object* x_516; 
lean_dec(x_7);
lean_inc(x_2);
x_516 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_516) == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = lean_ctor_get(x_516, 1);
lean_inc(x_517);
lean_dec(x_516);
x_518 = lean_unsigned_to_nat(0u);
x_519 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_518);
lean_inc(x_2);
x_520 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_517);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; uint8_t x_553; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_521, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_520, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_524 = x_520;
} else {
 lean_dec_ref(x_520);
 x_524 = lean_box(0);
}
x_525 = lean_ctor_get(x_521, 0);
lean_inc(x_525);
lean_dec(x_521);
x_526 = lean_ctor_get(x_522, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_522, 1);
lean_inc(x_527);
lean_dec(x_522);
x_553 = lean_unbox(x_527);
if (x_553 == 0)
{
lean_object* x_554; 
x_554 = lean_array_get_size(x_6);
x_528 = x_554;
goto block_552;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_array_get_size(x_6);
x_556 = lean_unsigned_to_nat(1u);
x_557 = lean_nat_sub(x_555, x_556);
lean_dec(x_555);
x_528 = x_557;
goto block_552;
}
block_552:
{
uint8_t x_529; 
x_529 = lean_nat_dec_lt(x_526, x_528);
if (x_529 == 0)
{
lean_object* x_530; 
lean_dec(x_524);
lean_inc(x_8);
x_530 = l_Lean_Meta_inferType(x_525, x_8, x_523);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = l_Lean_Expr_getAppNumArgsAux___main(x_531, x_518);
x_534 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_533);
x_535 = lean_mk_array(x_533, x_534);
x_536 = lean_unsigned_to_nat(1u);
x_537 = lean_nat_sub(x_533, x_536);
lean_dec(x_533);
x_538 = lean_unbox(x_527);
lean_dec(x_527);
x_539 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_519, x_526, x_538, x_528, x_531, x_535, x_537, x_8, x_532);
return x_539;
}
else
{
uint8_t x_540; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_519);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_540 = !lean_is_exclusive(x_530);
if (x_540 == 0)
{
return x_530;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_541 = lean_ctor_get(x_530, 0);
x_542 = lean_ctor_get(x_530, 1);
lean_inc(x_542);
lean_inc(x_541);
lean_dec(x_530);
x_543 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_543, 0, x_541);
lean_ctor_set(x_543, 1, x_542);
return x_543;
}
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_525);
lean_dec(x_519);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_544 = l_Lean_Name_toString___closed__1;
x_545 = l_Lean_Name_toStringWithSep___main(x_544, x_2);
x_546 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_547 = lean_string_append(x_546, x_545);
lean_dec(x_545);
x_548 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_549 = lean_string_append(x_547, x_548);
x_550 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_550, 0, x_549);
if (lean_is_scalar(x_524)) {
 x_551 = lean_alloc_ctor(1, 2, 0);
} else {
 x_551 = x_524;
 lean_ctor_set_tag(x_551, 1);
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_523);
return x_551;
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_519);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_520);
if (x_558 == 0)
{
return x_520;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_520, 0);
x_560 = lean_ctor_get(x_520, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_520);
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
x_562 = !lean_is_exclusive(x_516);
if (x_562 == 0)
{
return x_516;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_516, 0);
x_564 = lean_ctor_get(x_516, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_516);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
default: 
{
lean_object* x_566; 
lean_dec(x_7);
lean_inc(x_2);
x_566 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive(x_2, x_5, x_6, x_8, x_9);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = lean_unsigned_to_nat(0u);
x_569 = l___private_Init_Lean_Meta_RecursorInfo_4__getNumParams___main(x_4, x_5, x_568);
lean_inc(x_2);
x_570 = l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim(x_2, x_3, x_4, x_5, x_6, x_8, x_567);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_603; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
x_573 = lean_ctor_get(x_570, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_574 = x_570;
} else {
 lean_dec_ref(x_570);
 x_574 = lean_box(0);
}
x_575 = lean_ctor_get(x_571, 0);
lean_inc(x_575);
lean_dec(x_571);
x_576 = lean_ctor_get(x_572, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_603 = lean_unbox(x_577);
if (x_603 == 0)
{
lean_object* x_604; 
x_604 = lean_array_get_size(x_6);
x_578 = x_604;
goto block_602;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_array_get_size(x_6);
x_606 = lean_unsigned_to_nat(1u);
x_607 = lean_nat_sub(x_605, x_606);
lean_dec(x_605);
x_578 = x_607;
goto block_602;
}
block_602:
{
uint8_t x_579; 
x_579 = lean_nat_dec_lt(x_576, x_578);
if (x_579 == 0)
{
lean_object* x_580; 
lean_dec(x_574);
lean_inc(x_8);
x_580 = l_Lean_Meta_inferType(x_575, x_8, x_573);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; uint8_t x_588; lean_object* x_589; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = l_Lean_Expr_getAppNumArgsAux___main(x_581, x_568);
x_584 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_583);
x_585 = lean_mk_array(x_583, x_584);
x_586 = lean_unsigned_to_nat(1u);
x_587 = lean_nat_sub(x_583, x_586);
lean_dec(x_583);
x_588 = lean_unbox(x_577);
lean_dec(x_577);
x_589 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_4, x_5, x_6, x_569, x_576, x_588, x_578, x_581, x_585, x_587, x_8, x_582);
return x_589;
}
else
{
uint8_t x_590; 
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_569);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_590 = !lean_is_exclusive(x_580);
if (x_590 == 0)
{
return x_580;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_580, 0);
x_592 = lean_ctor_get(x_580, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_580);
x_593 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_593, 0, x_591);
lean_ctor_set(x_593, 1, x_592);
return x_593;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
lean_dec(x_578);
lean_dec(x_577);
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_569);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_594 = l_Lean_Name_toString___closed__1;
x_595 = l_Lean_Name_toStringWithSep___main(x_594, x_2);
x_596 = l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1;
x_597 = lean_string_append(x_596, x_595);
lean_dec(x_595);
x_598 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1;
x_599 = lean_string_append(x_597, x_598);
x_600 = lean_alloc_ctor(20, 1, 0);
lean_ctor_set(x_600, 0, x_599);
if (lean_is_scalar(x_574)) {
 x_601 = lean_alloc_ctor(1, 2, 0);
} else {
 x_601 = x_574;
 lean_ctor_set_tag(x_601, 1);
}
lean_ctor_set(x_601, 0, x_600);
lean_ctor_set(x_601, 1, x_573);
return x_601;
}
}
}
else
{
uint8_t x_608; 
lean_dec(x_569);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_608 = !lean_is_exclusive(x_570);
if (x_608 == 0)
{
return x_570;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_570, 0);
x_610 = lean_ctor_get(x_570, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_570);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
else
{
uint8_t x_612; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_566);
if (x_612 == 0)
{
return x_566;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_566, 0);
x_614 = lean_ctor_get(x_566, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_566);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_11, x_13, x_6, x_7);
return x_14;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_ConstantInfo_name(x_1);
lean_inc(x_5);
x_6 = l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f(x_5, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_ConstantInfo_type(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed), 7, 3);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1___boxed(lean_object** _args) {
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
x_19 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_12, x_13, x_14, x_15, x_16, x_17);
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
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of argument");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("major premise position must be greater than 0");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(lean_object* x_1) {
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
x_10 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
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
x_16 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4;
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2;
return x_18;
}
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_8, x_3, x_7);
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
x_11 = l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_2, x_3, x_10);
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
lean_object* l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_1, x_3);
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
x_13 = l___private_Init_Lean_Environment_5__envExtensionsRef;
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
x_18 = l_Lean_registerEnvExtensionUnsafe___at_Lean_registerTagAttribute___spec__4___closed__1;
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_io_ref_get(x_13, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_io_ref_reset(x_13, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_registerEnvExtensionUnsafe___rarg___closed__3;
lean_inc(x_19);
x_26 = x_19;
x_27 = lean_array_push(x_21, x_26);
x_28 = lean_io_ref_set(x_13, x_27, x_24);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_19);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_19);
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
lean_dec(x_21);
lean_dec(x_19);
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
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_20);
if (x_41 == 0)
{
return x_20;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_14);
if (x_45 == 0)
{
return x_14;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_14, 0);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_3);
if (x_49 == 0)
{
return x_3;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_3, 0);
x_51 = lean_ctor_get(x_3, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_3);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Init_Lean_Environment_8__persistentEnvExtensionsRef;
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_io_ref_reset(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_22);
x_29 = x_22;
x_30 = lean_array_push(x_24, x_29);
x_31 = lean_io_ref_set(x_3, x_30, x_27);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_22);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_22);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
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
lean_dec(x_24);
lean_dec(x_22);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
lean_dec(x_22);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
lean_dec(x_1);
x_53 = l_Lean_Name_toString___closed__1;
x_54 = l_Lean_Name_toStringWithSep___main(x_53, x_52);
x_55 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_56 = lean_string_append(x_55, x_54);
lean_dec(x_54);
x_57 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_58 = lean_string_append(x_56, x_57);
x_59 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_59);
return x_4;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_4, 0);
x_61 = lean_ctor_get(x_4, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_4);
x_62 = lean_array_get_size(x_60);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_anyRangeMAux___main___at_Lean_Meta_mkRecursorAttr___spec__6(x_1, x_60, x_60, x_62, x_63);
lean_dec(x_62);
lean_dec(x_60);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 4);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 5);
lean_inc(x_70);
lean_dec(x_1);
x_71 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_72 = lean_alloc_closure((void*)(l_EStateM_bind___rarg), 3, 2);
lean_closure_set(x_72, 0, x_66);
lean_closure_set(x_72, 1, x_71);
x_73 = l_Lean_registerEnvExtensionUnsafe___at_Lean_Meta_mkRecursorAttr___spec__7(x_72, x_61);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_65);
lean_ctor_set(x_76, 2, x_67);
lean_ctor_set(x_76, 3, x_68);
lean_ctor_set(x_76, 4, x_69);
lean_ctor_set(x_76, 5, x_70);
x_77 = lean_io_ref_get(x_3, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_io_ref_reset(x_3, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__2;
lean_inc(x_76);
x_83 = x_76;
x_84 = lean_array_push(x_78, x_83);
x_85 = lean_io_ref_set(x_3, x_84, x_81);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_76);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
x_89 = lean_ctor_get(x_85, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_91 = x_85;
} else {
 lean_dec_ref(x_85);
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
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_78);
lean_dec(x_76);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_95 = x_80;
} else {
 lean_dec_ref(x_80);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_76);
x_97 = lean_ctor_get(x_77, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_77, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_99 = x_77;
} else {
 lean_dec_ref(x_77);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_65);
x_101 = lean_ctor_get(x_73, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_73, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_103 = x_73;
} else {
 lean_dec_ref(x_73);
 x_103 = lean_box(0);
}
if (lean_is_scalar(x_103)) {
 x_104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_104 = x_103;
}
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_102);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
lean_dec(x_1);
x_106 = l_Lean_Name_toString___closed__1;
x_107 = l_Lean_Name_toStringWithSep___main(x_106, x_105);
x_108 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__3;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__4;
x_111 = lean_string_append(x_109, x_110);
x_112 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_61);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
return x_4;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_2, x_1);
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
x_7 = l_Lean_registerTagAttribute___closed__1;
x_8 = l_Lean_registerTagAttribute___closed__2;
x_9 = l_Lean_registerParametricAttribute___rarg___closed__1;
x_10 = l_Lean_registerParametricAttribute___at_Lean_Meta_mkRecursorAttr___spec__1___closed__1;
x_11 = l_Lean_registerParametricAttribute___rarg___closed__2;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_registerParametricAttribute___rarg___lambda__4___boxed), 9, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_4);
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
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos(x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_mkRecursorAttr___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_RecursorInfo_14__mkRecursorInfoCore), 4, 2);
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
lean_object* l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_fold___main___at_Lean_Meta_mkRecursorAttr___spec__2(x_1, x_2);
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
lean_object* l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_6, x_3);
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
lean_object* l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Meta_getMajorPos_x3f___spec__2(x_1, x_2);
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
x_15 = l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec(x_1, x_14, x_3, x_7);
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
x_17 = l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_2, x_3, x_7);
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
x_12 = l___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux(x_6, x_11, x_3, x_7);
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
lean_object* initialize_Init_Data_Nat_Control(lean_object*);
lean_object* initialize_Init_Lean_AuxRecursor(lean_object*);
lean_object* initialize_Init_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_Message(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_RecursorInfo(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_AuxRecursor(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Message(lean_io_mk_world());
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
l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_1__mkRecursorInfoForKernelRec___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_2__getMajorPosIfAuxRecursor_x3f___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3 = _init_l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_3__checkMotive___closed__3);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__3);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__4);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__6);
l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7 = _init_l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__7);
l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_6__getParamsPos___spec__2___closed__1);
l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1 = _init_l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1();
lean_mark_persistent(l_Nat_foldMAux___main___at___private_Init_Lean_Meta_RecursorInfo_7__getIndicesPos___spec__2___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_8__getMotiveLevel___closed__1);
l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1 = _init_l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Init_Lean_Meta_RecursorInfo_9__getUnivLevelPos___spec__2___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_10__getProduceMotiveAndRecursive___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3 = _init_l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_11__checkMotiveResultType___closed__3);
l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__1___closed__1);
l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___main___at___private_Init_Lean_Meta_RecursorInfo_12__mkRecursorInfoAux___spec__2___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1 = _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__1);
l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2 = _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__2);
l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3 = _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__3);
l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4 = _init_l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_RecursorInfo_13__syntaxToMajorPos___closed__4);
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
