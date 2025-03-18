// Lean compiler output
// Module: Lean.Meta.RecursorInfo
// Imports: Lean.AuxRecursor Lean.Util.FindExpr Lean.Meta.Basic
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__3;
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1;
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1;
static lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__11;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_getAttrParamOptPrio___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_casesOnSuffix;
static uint64_t l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7;
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__5;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__13;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6;
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__6;
extern lean_object* l_instInhabitedNat;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_recursorAttribute;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(lean_object*, size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6;
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__9;
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__17;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_instToString___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__10;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1;
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806_(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__1;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString(lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2;
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_recOnSuffix;
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__4;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2;
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2;
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_brecOnSuffix;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_addParenHeuristic(lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10;
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4;
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString___lambda__1___boxed(lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__8;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1___boxed(lean_object**);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object*, lean_object*);
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3;
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__15;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1;
lean_object* l_Lean_registerParametricAttribute___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8;
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__18;
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2;
static lean_object* l_Lean_Meta_getMajorPos_x3f___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5___boxed(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__16;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__2;
static lean_object* l_Lean_Meta_RecursorInfo_instToString___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1;
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___boxed(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2;
static lean_object* _init_l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<motive-univ>", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToStringRecursorUnivLevelPos(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 5);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numParams___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numParams(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 6);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthTRAux___rarg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numIndices___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numIndices(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numParams(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_motivePos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_motivePos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_firstIndexPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_firstIndexPos(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_isMinor(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_isMinor___boxed(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_numMinors___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_RecursorInfo_numMinors(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1;
x_6 = lean_string_append(x_1, x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_string_append(x_6, x_11);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_2 = l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3;
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_8 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; uint32_t x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = 93;
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3;
x_15 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2(x_14, x_3);
x_16 = lean_string_push(x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l___private_Init_Data_Repr_0__Nat_reprFast(x_17);
x_19 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_20 = lean_string_append(x_19, x_18);
lean_dec(x_18);
x_21 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2(x_20, x_3);
x_22 = lean_string_push(x_21, x_13);
return x_22;
}
}
}
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("none", 4, 4);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("(some ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1;
x_6 = lean_string_append(x_1, x_5);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = l_addParenHeuristic(x_11);
lean_dec(x_11);
x_13 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_string_append(x_6, x_16);
lean_dec(x_16);
x_1 = x_17;
x_2 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_2 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1;
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_8 = l_addParenHeuristic(x_7);
lean_dec(x_7);
x_9 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_16 = lean_string_append(x_14, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint32_t x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = 93;
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1;
x_20 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4(x_19, x_3);
x_21 = lean_string_push(x_20, x_18);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = l___private_Init_Data_Repr_0__Nat_reprFast(x_22);
x_24 = l_addParenHeuristic(x_23);
lean_dec(x_23);
x_25 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2;
x_26 = lean_string_append(x_25, x_24);
lean_dec(x_24);
x_27 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3;
x_28 = lean_string_append(x_26, x_27);
x_29 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4(x_30, x_3);
x_32 = lean_string_push(x_31, x_18);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_6 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__6(x_13, x_3);
x_15 = 93;
x_16 = lean_string_push(x_14, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_unbox(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1;
x_9 = lean_string_append(x_6, x_8);
x_1 = x_9;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2;
x_12 = lean_string_append(x_6, x_11);
x_1 = x_12;
x_2 = x_4;
goto _start;
}
}
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_2 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1;
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2;
x_2 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3;
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unbox(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4;
return x_7;
}
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = 93;
x_10 = lean_unbox(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1;
x_12 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8(x_11, x_3);
x_13 = lean_string_push(x_12, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3;
x_15 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8(x_14, x_3);
x_16 = lean_string_push(x_15, x_9);
return x_16;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_RecursorInfo_instToString___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  name           := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_RecursorInfo_instToString___closed__1;
x_2 = l_Lean_Meta_RecursorInfo_instToString___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_RecursorInfo_instToString___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  type           := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  univs          := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  depElim        := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  recursive      := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  numArgs        := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  numParams      := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  numIndices     := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  numMinors      := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  major          := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  motive         := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  paramsAtMajor  := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  indicesAtMajor := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  produceMotive  := ", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_RecursorInfo_instToString___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("}", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = 1;
x_4 = l_Lean_Meta_RecursorInfo_instToString___closed__4;
x_5 = l_Lean_Name_toString(x_2, x_3, x_4);
x_6 = l_Lean_Meta_RecursorInfo_instToString___closed__3;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_Lean_Meta_RecursorInfo_instToString___closed__5;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_Lean_Meta_RecursorInfo_instToString___closed__6;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = l_Lean_Name_toString(x_12, x_3, x_4);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = lean_string_append(x_14, x_8);
x_16 = l_Lean_Meta_RecursorInfo_instToString___closed__7;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = lean_string_append(x_20, x_8);
x_22 = l_Lean_Meta_RecursorInfo_instToString___closed__8;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*8 + 1);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_28 = l_Lean_Meta_RecursorInfo_numParams(x_1);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_30 = l_Lean_Meta_RecursorInfo_numIndices(x_1);
x_31 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_32 = l_Lean_Meta_RecursorInfo_numMinors(x_1);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_34 = lean_ctor_get(x_1, 4);
lean_inc(x_34);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_34);
x_36 = lean_ctor_get(x_1, 5);
lean_inc(x_36);
x_37 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3(x_36);
x_38 = lean_ctor_get(x_1, 6);
lean_inc(x_38);
x_39 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__5(x_38);
x_40 = lean_ctor_get(x_1, 7);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7(x_40);
lean_dec(x_40);
if (x_24 == 0)
{
lean_object* x_92; 
x_92 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1;
x_42 = x_92;
goto block_91;
}
else
{
lean_object* x_93; 
x_93 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2;
x_42 = x_93;
goto block_91;
}
block_91:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_string_append(x_23, x_42);
lean_dec(x_42);
x_44 = lean_string_append(x_43, x_8);
x_45 = l_Lean_Meta_RecursorInfo_instToString___closed__9;
x_46 = lean_string_append(x_44, x_45);
if (x_25 == 0)
{
lean_object* x_89; 
x_89 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1;
x_47 = x_89;
goto block_88;
}
else
{
lean_object* x_90; 
x_90 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2;
x_47 = x_90;
goto block_88;
}
block_88:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_string_append(x_48, x_8);
x_50 = l_Lean_Meta_RecursorInfo_instToString___closed__10;
x_51 = lean_string_append(x_49, x_50);
x_52 = lean_string_append(x_51, x_27);
lean_dec(x_27);
x_53 = lean_string_append(x_52, x_8);
x_54 = l_Lean_Meta_RecursorInfo_instToString___closed__11;
x_55 = lean_string_append(x_53, x_54);
x_56 = lean_string_append(x_55, x_29);
x_57 = lean_string_append(x_56, x_8);
x_58 = l_Lean_Meta_RecursorInfo_instToString___closed__12;
x_59 = lean_string_append(x_57, x_58);
x_60 = lean_string_append(x_59, x_31);
lean_dec(x_31);
x_61 = lean_string_append(x_60, x_8);
x_62 = l_Lean_Meta_RecursorInfo_instToString___closed__13;
x_63 = lean_string_append(x_61, x_62);
x_64 = lean_string_append(x_63, x_33);
lean_dec(x_33);
x_65 = lean_string_append(x_64, x_8);
x_66 = l_Lean_Meta_RecursorInfo_instToString___closed__14;
x_67 = lean_string_append(x_65, x_66);
x_68 = lean_string_append(x_67, x_35);
lean_dec(x_35);
x_69 = lean_string_append(x_68, x_8);
x_70 = l_Lean_Meta_RecursorInfo_instToString___closed__15;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_string_append(x_71, x_29);
lean_dec(x_29);
x_73 = lean_string_append(x_72, x_8);
x_74 = l_Lean_Meta_RecursorInfo_instToString___closed__16;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_string_append(x_75, x_37);
lean_dec(x_37);
x_77 = lean_string_append(x_76, x_8);
x_78 = l_Lean_Meta_RecursorInfo_instToString___closed__17;
x_79 = lean_string_append(x_77, x_78);
x_80 = lean_string_append(x_79, x_39);
lean_dec(x_39);
x_81 = lean_string_append(x_80, x_8);
x_82 = l_Lean_Meta_RecursorInfo_instToString___closed__18;
x_83 = lean_string_append(x_81, x_82);
x_84 = lean_string_append(x_83, x_41);
lean_dec(x_41);
x_85 = lean_string_append(x_84, x_8);
x_86 = l_Lean_Meta_RecursorInfo_instToString___closed__19;
x_87 = lean_string_append(x_85, x_86);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_RecursorInfo_instToString___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_RecursorInfo_instToString___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a recursor", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 7)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = 0;
x_17 = l_Lean_MessageData_ofConstName(x_1, x_16);
x_18 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2(x_21, x_2, x_3, x_4, x_5, x_15);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rec", 3, 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_is_aux_recursor(x_12, x_1);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_54; uint8_t x_55; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_54 = l_Lean_recOnSuffix;
x_55 = lean_string_dec_eq(x_16, x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_casesOnSuffix;
x_57 = lean_string_dec_eq(x_16, x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_brecOnSuffix;
x_59 = lean_string_dec_eq(x_16, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_16);
lean_dec(x_15);
x_60 = lean_box(0);
lean_ctor_set(x_8, 0, x_60);
return x_8;
}
else
{
lean_object* x_61; 
lean_free_object(x_8);
x_61 = lean_box(0);
x_17 = x_61;
goto block_53;
}
}
else
{
lean_object* x_62; 
lean_free_object(x_8);
x_62 = lean_box(0);
x_17 = x_62;
goto block_53;
}
}
else
{
lean_object* x_63; 
lean_free_object(x_8);
x_63 = lean_box(0);
x_17 = x_63;
goto block_53;
}
block_53:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
x_18 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1;
x_19 = l_Lean_Name_str___override(x_15, x_18);
x_20 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1(x_19, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 3);
lean_inc(x_24);
x_25 = lean_nat_add(x_23, x_24);
lean_dec(x_24);
lean_dec(x_23);
x_26 = l_Lean_casesOnSuffix;
x_27 = lean_string_dec_eq(x_16, x_26);
lean_dec(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 4);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_nat_add(x_25, x_28);
lean_dec(x_28);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_20, 0, x_30);
return x_20;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_25, x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_20, 0, x_33);
return x_20;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 3);
lean_inc(x_37);
x_38 = lean_nat_add(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_casesOnSuffix;
x_40 = lean_string_dec_eq(x_16, x_39);
lean_dec(x_16);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 4);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_nat_add(x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_38, x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
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
lean_dec(x_16);
x_49 = !lean_is_exclusive(x_20);
if (x_49 == 0)
{
return x_20;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_20, 0);
x_51 = lean_ctor_get(x_20, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_20);
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
lean_object* x_64; 
lean_dec(x_1);
x_64 = lean_box(0);
lean_ctor_set(x_8, 0, x_64);
return x_8;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_8, 0);
x_66 = lean_ctor_get(x_8, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_8);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_1);
x_68 = lean_is_aux_recursor(x_67, x_1);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_98; uint8_t x_99; 
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
lean_dec(x_1);
x_98 = l_Lean_recOnSuffix;
x_99 = lean_string_dec_eq(x_72, x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = l_Lean_casesOnSuffix;
x_101 = lean_string_dec_eq(x_72, x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_brecOnSuffix;
x_103 = lean_string_dec_eq(x_72, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_72);
lean_dec(x_71);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_66);
return x_105;
}
else
{
lean_object* x_106; 
x_106 = lean_box(0);
x_73 = x_106;
goto block_97;
}
}
else
{
lean_object* x_107; 
x_107 = lean_box(0);
x_73 = x_107;
goto block_97;
}
}
else
{
lean_object* x_108; 
x_108 = lean_box(0);
x_73 = x_108;
goto block_97;
}
block_97:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_73);
x_74 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1;
x_75 = l_Lean_Name_str___override(x_71, x_74);
x_76 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1(x_75, x_3, x_4, x_5, x_6, x_66);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_79 = x_76;
} else {
 lean_dec_ref(x_76);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_77, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 3);
lean_inc(x_81);
x_82 = lean_nat_add(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
x_83 = l_Lean_casesOnSuffix;
x_84 = lean_string_dec_eq(x_72, x_83);
lean_dec(x_72);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_77, 4);
lean_inc(x_85);
lean_dec(x_77);
x_86 = lean_nat_add(x_82, x_85);
lean_dec(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_77);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_nat_add(x_82, x_89);
lean_dec(x_82);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_79)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_79;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_78);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_72);
x_93 = lean_ctor_get(x_76, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_95 = x_76;
} else {
 lean_dec_ref(x_76);
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
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_1);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_66);
return x_110;
}
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_1);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Expr_isFVar(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid user defined recursor '", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', result type must be of the form (C t), where C is a bound variable, and t is a (possibly empty) sequence of bound variables", 126, 126);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_17; 
x_17 = l_Lean_Expr_isFVar(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_9 = x_18;
goto block_16;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_array_get_size(x_3);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
else
{
size_t x_24; size_t x_25; uint8_t x_26; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_26 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(x_3, x_24, x_25);
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
goto block_16;
}
}
}
block_16:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_14, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
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
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_expr_eqv(x_7, x_2);
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
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_expr_eqv(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
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
LEAN_EXPORT uint8_t l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6(x_2, x_1, x_7, x_8);
return x_9;
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed recursor '", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_Array_back_x21___rarg(x_10, x_1);
x_12 = l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1(x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_13 = l_Lean_MessageData_ofName(x_3);
x_14 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid user defined recursor, '", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not support dependent elimination, and position of the major premise was not specified (solution: set attribute '[recursor <pos>]', where <pos> is the position of the major premise)", 188, 188);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid major premise position for user defined recursor, recursor has only ", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" arguments", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = l_Array_isEmpty___rarg(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1(x_4, x_3, x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = l_Lean_MessageData_ofName(x_1);
x_14 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_17, x_5, x_6, x_7, x_8, x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_array_get_size(x_3);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_24);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_27);
x_28 = l_Lean_MessageData_ofFormat(x_2);
x_29 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_32, x_5, x_6, x_7, x_8, x_9);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_25);
lean_free_object(x_2);
x_34 = lean_array_fget(x_3, x_24);
x_35 = l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5(x_4, x_34);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_24);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_array_get_size(x_3);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_40);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
x_44 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_MessageData_ofFormat(x_44);
x_46 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_49, x_5, x_6, x_7, x_8, x_9);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
x_51 = lean_array_fget(x_3, x_40);
x_52 = l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5(x_4, x_51);
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_9);
return x_56;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_idxOfAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_idxOf_x3f___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_20 = l_Lean_Meta_isExprDefEq(x_16, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_8);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
lean_inc(x_4);
x_25 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(x_4, x_18, x_24, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
x_7 = x_30;
x_8 = x_28;
x_13 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
lean_inc(x_18);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_8, 0, x_35);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
lean_inc(x_18);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_18);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_8, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_8);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_45 = l_Lean_Meta_isExprDefEq(x_16, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_box(0);
lean_inc(x_4);
x_50 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(x_4, x_44, x_49, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_44);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = 1;
x_55 = lean_usize_add(x_7, x_54);
x_7 = x_55;
x_8 = x_53;
x_13 = x_52;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
lean_inc(x_44);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_44);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_44);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_45, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_65 = x_45;
} else {
 lean_dec_ref(x_45);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', type of the major premise does not contain the recursor parameter", 68, 68);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_nat_dec_lt(x_7, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_60; lean_object* x_61; size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_2, x_7);
x_60 = lean_box(0);
x_61 = lean_box(0);
x_62 = lean_array_size(x_3);
x_63 = 0;
x_64 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_26);
x_65 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1(x_3, x_26, x_60, x_61, x_3, x_62, x_63, x_64, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_27 = x_61;
x_28 = x_68;
goto block_59;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_27 = x_70;
x_28 = x_69;
goto block_59;
}
}
else
{
uint8_t x_71; 
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_5, 2);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_6 = x_20;
x_7 = x_22;
x_8 = lean_box(0);
x_9 = lean_box(0);
x_14 = x_19;
goto _start;
}
block_59:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_Lean_Expr_fvarId_x21(x_26);
lean_dec(x_26);
lean_inc(x_10);
x_30 = l_Lean_FVarId_getDecl(x_29, x_10, x_11, x_12, x_13, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_LocalDecl_binderInfo(x_31);
lean_dec(x_31);
x_34 = l_Lean_BinderInfo_isInstImplicit(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
x_35 = l_Lean_MessageData_ofName(x_1);
x_36 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_39, x_10, x_11, x_12, x_13, x_32);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_box(0);
x_46 = lean_array_push(x_6, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_18 = x_47;
x_19 = x_32;
goto block_24;
}
}
else
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_26);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_array_push(x_6, x_27);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_18 = x_54;
x_19 = x_28;
goto block_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_27, 0);
lean_inc(x_55);
lean_dec(x_27);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_array_push(x_6, x_56);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_18 = x_58;
x_19 = x_28;
goto block_24;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_3);
lean_ctor_set(x_12, 2, x_11);
x_13 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
x_14 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2(x_1, x_2, x_4, x_12, x_12, x_13, x_10, lean_box(0), lean_box(0), x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_to_list(x_16);
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
x_20 = lean_array_to_list(x_18);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_20 = l_Lean_Meta_isExprDefEq(x_16, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
lean_free_object(x_8);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(0);
lean_inc(x_4);
x_25 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(x_4, x_18, x_24, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = lean_usize_add(x_7, x_29);
x_7 = x_30;
x_8 = x_28;
x_13 = x_27;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
lean_dec(x_33);
lean_inc(x_18);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_18);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_8, 0, x_35);
lean_ctor_set(x_20, 0, x_8);
return x_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_dec(x_20);
lean_inc(x_18);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_18);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_8, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_8);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_8, 1);
lean_inc(x_44);
lean_dec(x_8);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_45 = l_Lean_Meta_isExprDefEq(x_16, x_2, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; size_t x_55; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_box(0);
lean_inc(x_4);
x_50 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__1___lambda__1(x_4, x_44, x_49, x_9, x_10, x_11, x_12, x_48);
lean_dec(x_44);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = 1;
x_55 = lean_usize_add(x_7, x_54);
x_7 = x_55;
x_8 = x_53;
x_13 = x_52;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_58 = x_45;
} else {
 lean_dec_ref(x_45);
 x_58 = lean_box(0);
}
lean_inc(x_44);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_44);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_44);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_45, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_45, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_65 = x_45;
} else {
 lean_dec_ref(x_45);
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
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', type of the major premise does not contain the recursor index", 64, 64);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_nat_dec_lt(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_nat_sub(x_3, x_4);
x_39 = lean_nat_add(x_38, x_9);
lean_dec(x_38);
x_40 = l_Lean_instInhabitedExpr;
x_41 = lean_array_get(x_40, x_2, x_39);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = lean_box(0);
x_44 = lean_array_size(x_5);
x_45 = 0;
x_46 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3;
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_47 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1(x_5, x_41, x_42, x_43, x_5, x_44, x_45, x_46, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_20 = x_43;
x_21 = x_50;
goto block_37;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_20 = x_52;
x_21 = x_51;
goto block_37;
}
}
else
{
uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_47);
if (x_53 == 0)
{
return x_47;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_47, 0);
x_55 = lean_ctor_get(x_47, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_47);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
block_37:
{
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
x_22 = l_Lean_MessageData_ofName(x_1);
x_23 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_26, x_12, x_13, x_14, x_15, x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_20, 0);
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_array_push(x_8, x_32);
x_34 = lean_ctor_get(x_7, 2);
x_35 = lean_nat_add(x_9, x_34);
lean_dec(x_9);
x_8 = x_33;
x_9 = x_35;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_16 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(1u);
lean_inc(x_4);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_12);
x_14 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
x_15 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_13, x_13, x_14, x_11, lean_box(0), lean_box(0), x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
lean_dec(x_4);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_to_list(x_17);
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
x_21 = lean_array_to_list(x_19);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', motive result sort must be Prop or (Sort u) where u is a universe level parameter", 84, 84);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
case 4:
{
lean_object* x_10; 
lean_dec(x_1);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_MessageData_ofName(x_1);
x_12 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1(x_15, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = l_Lean_MessageData_ofName(x_1);
x_18 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1(x_21, x_3, x_4, x_5, x_6, x_7);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_level_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', major premise type does not contain universe level parameter '", 65, 65);
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
x_19 = l_Lean_Level_param___override(x_17);
x_20 = lean_level_eq(x_3, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_findIdx_x3f_loop___rarg(x_21, x_4, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_8);
x_24 = l_Lean_MessageData_ofName(x_1);
x_25 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_24);
lean_ctor_set(x_7, 0, x_25);
x_26 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofName(x_17);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_31, x_10, x_11, x_12, x_13, x_14);
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
uint8_t x_37; 
lean_free_object(x_7);
lean_dec(x_17);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_array_push(x_8, x_23);
x_7 = x_18;
x_8 = x_38;
x_9 = lean_box(0);
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_23, 0);
lean_inc(x_40);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_array_push(x_8, x_41);
x_7 = x_18;
x_8 = x_42;
x_9 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_19);
lean_free_object(x_7);
lean_dec(x_17);
x_44 = lean_box(0);
x_45 = lean_array_push(x_8, x_44);
x_7 = x_18;
x_8 = x_45;
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
lean_inc(x_47);
x_49 = l_Lean_Level_param___override(x_47);
x_50 = lean_level_eq(x_3, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_51, 0, x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_findIdx_x3f_loop___rarg(x_51, x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_48);
lean_dec(x_8);
x_54 = l_Lean_MessageData_ofName(x_1);
x_55 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_MessageData_ofName(x_47);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__1(x_62, x_10, x_11, x_12, x_13, x_14);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_47);
x_68 = lean_ctor_get(x_53, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_69 = x_53;
} else {
 lean_dec_ref(x_53);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_array_push(x_8, x_70);
x_7 = x_48;
x_8 = x_71;
x_9 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_49);
lean_dec(x_47);
x_73 = lean_box(0);
x_74 = lean_array_push(x_8, x_73);
x_7 = x_48;
x_8 = x_74;
x_9 = lean_box(0);
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_mk(x_4);
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
lean_inc(x_2);
x_13 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1(x_1, x_2, x_3, x_10, x_11, x_2, x_2, x_12, lean_box(0), x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
lean_dec(x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_array_to_list(x_15);
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
x_19 = lean_array_to_list(x_17);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_infer_type(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = lean_find_expr(x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
if (lean_obj_tag(x_17) == 0)
{
size_t x_18; size_t x_19; 
lean_free_object(x_12);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = lean_find_expr(x_25, x_23);
lean_dec(x_23);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
size_t x_27; size_t x_28; 
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_9 = x_24;
goto _start;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_30 = 1;
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_12);
if (x_33 == 0)
{
return x_12;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_12, 0);
x_35 = lean_ctor_get(x_12, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_12);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_9);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_array_get_size(x_4);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_1);
x_25 = 0;
x_26 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(x_21, x_25, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_26;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1(x_1, x_4, x_27, x_28, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_unbox(x_30);
lean_dec(x_30);
x_33 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(x_21, x_32, x_8, x_9, x_10, x_11, x_31);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
lean_object* x_38; 
lean_dec(x_1);
x_38 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(x_21, x_3, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_38;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_infer_type(x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(x_5);
x_17 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___boxed), 10, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_16);
x_18 = 0;
x_19 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_14, x_17, x_18, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_4, x_5);
x_15 = lean_nat_dec_le(x_14, x_2);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2(x_1, x_2, x_3, x_6, x_7, x_16, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_2, x_4);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2(x_1, x_2, x_3, x_6, x_7, x_19, x_9, x_10, x_11, x_12, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
x_21 = lean_box(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_nat_dec_lt(x_8, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_nat_dec_lt(x_8, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_free_object(x_7);
x_25 = lean_box(0);
x_26 = lean_unbox(x_21);
lean_dec(x_21);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_27 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3(x_1, x_8, x_5, x_4, x_3, x_20, x_26, x_25, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_6, 2);
x_38 = lean_nat_add(x_8, x_37);
lean_dec(x_8);
x_7 = x_36;
x_8 = x_38;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_15 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
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
x_44 = lean_ctor_get(x_6, 2);
x_45 = lean_nat_add(x_8, x_44);
lean_dec(x_8);
x_8 = x_45;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_add(x_2, x_49);
x_51 = lean_nat_dec_lt(x_8, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_52 = lean_box(0);
x_53 = lean_unbox(x_48);
lean_dec(x_48);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
x_54 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3(x_1, x_8, x_5, x_4, x_3, x_47, x_53, x_52, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
lean_dec(x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_dec(x_54);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
lean_dec(x_55);
x_62 = lean_ctor_get(x_6, 2);
x_63 = lean_nat_add(x_8, x_62);
lean_dec(x_8);
x_7 = x_61;
x_8 = x_63;
x_9 = lean_box(0);
x_10 = lean_box(0);
x_15 = x_60;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_65 = lean_ctor_get(x_54, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_67 = x_54;
} else {
 lean_dec_ref(x_54);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_47);
lean_ctor_set(x_69, 1, x_48);
x_70 = lean_ctor_get(x_6, 2);
x_71 = lean_nat_add(x_8, x_70);
lean_dec(x_8);
x_7 = x_69;
x_8 = x_71;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1;
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_12, lean_box(0), lean_box(0), x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_array_to_list(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_array_to_list(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_31 = lean_array_to_list(x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
return x_16;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_16, 0);
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_16);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___lambda__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__2(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', motive must have a type of the form (C : Pi (i : B A), I A i -> Type), where A is (possibly empty) sequence of variables (aka parameters), (i : B A) is a (possibly empty) telescope (aka indices), and I is a constant", 218, 218);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_18; 
x_18 = l_Lean_Expr_isSort(x_3);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_10 = x_19;
goto block_17;
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
lean_object* x_23; 
x_23 = lean_box(0);
x_10 = x_23;
goto block_17;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_9);
return x_25;
}
}
block_17:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
x_11 = l_Lean_MessageData_ofName(x_1);
x_12 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
lean_inc(x_1);
x_21 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType(x_1, x_2, x_15, x_14, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_1);
x_23 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel(x_1, x_15, x_16, x_17, x_18, x_19, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_ConstantInfo_levelParams(x_3);
lean_inc(x_1);
x_27 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos(x_1, x_26, x_24, x_4, x_16, x_17, x_18, x_19, x_25);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive(x_5, x_6, x_7, x_8, x_9, x_16, x_17, x_18, x_19, x_29);
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
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', type of the major premise must be of the form (I ...), where I is a constant", 79, 79);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
lean_inc(x_1);
x_20 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos(x_1, x_3, x_6, x_11, x_13, x_14, x_15, x_16, x_17);
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
lean_inc(x_1);
x_23 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos(x_1, x_3, x_7, x_9, x_11, x_13, x_14, x_15, x_16, x_22);
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
x_26 = lean_infer_type(x_4, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(x_8);
x_30 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1___boxed), 20, 13);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_5);
lean_closure_set(x_30, 2, x_2);
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
x_31 = 0;
x_32 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_27, x_30, x_31, x_13, x_14, x_15, x_16, x_28);
return x_32;
}
else
{
uint8_t x_33; 
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
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
return x_26;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_26, 0);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_26);
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
case 5:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_dec(x_10);
x_47 = lean_array_set(x_11, x_12, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_12, x_48);
lean_dec(x_12);
x_10 = x_45;
x_11 = x_47;
x_12 = x_49;
goto _start;
}
default: 
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = l_Lean_MessageData_ofName(x_1);
x_52 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1(x_55, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_17 = lean_infer_type(x_1, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_18, x_20);
x_22 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
x_26 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18, x_23, x_25, x_12, x_13, x_14, x_15, x_19);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', indices must occur before major premise", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_7);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_15);
lean_inc(x_1);
x_17 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_42; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_22 = x_18;
} else {
 lean_dec_ref(x_18);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_25 = x_19;
} else {
 lean_dec_ref(x_19);
 x_25 = lean_box(0);
}
x_42 = lean_unbox(x_24);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_array_get_size(x_6);
x_26 = x_43;
goto block_41;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_array_get_size(x_6);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_44, x_45);
lean_dec(x_44);
x_26 = x_46;
goto block_41;
}
block_41:
{
uint8_t x_27; 
x_27 = lean_nat_dec_lt(x_23, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_22);
x_28 = lean_box(0);
x_29 = lean_unbox(x_24);
lean_dec(x_24);
x_30 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_21, x_1, x_2, x_4, x_5, x_6, x_16, x_23, x_29, x_26, x_28, x_8, x_9, x_10, x_11, x_20);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = l_Lean_MessageData_ofName(x_1);
x_32 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_25)) {
 x_33 = lean_alloc_ctor(7, 2, 0);
} else {
 x_33 = x_25;
 lean_ctor_set_tag(x_33, 7);
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_22)) {
 x_35 = lean_alloc_ctor(7, 2, 0);
} else {
 x_35 = x_22;
 lean_ctor_set_tag(x_35, 7);
}
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_35, x_8, x_9, x_10, x_11, x_20);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
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
uint8_t x_47; 
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
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
return x_17;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_17, 0);
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
case 1:
{
lean_object* x_55; 
lean_dec(x_7);
lean_inc(x_1);
x_55 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_57);
lean_inc(x_1);
x_59 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_84; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_67 = x_61;
} else {
 lean_dec_ref(x_61);
 x_67 = lean_box(0);
}
x_84 = lean_unbox(x_66);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_array_get_size(x_6);
x_68 = x_85;
goto block_83;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_array_get_size(x_6);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_86, x_87);
lean_dec(x_86);
x_68 = x_88;
goto block_83;
}
block_83:
{
uint8_t x_69; 
x_69 = lean_nat_dec_lt(x_65, x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
lean_dec(x_67);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_unbox(x_66);
lean_dec(x_66);
x_72 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_63, x_1, x_2, x_4, x_5, x_6, x_58, x_65, x_71, x_68, x_70, x_8, x_9, x_10, x_11, x_62);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_73 = l_Lean_MessageData_ofName(x_1);
x_74 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_67;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_64)) {
 x_77 = lean_alloc_ctor(7, 2, 0);
} else {
 x_77 = x_64;
 lean_ctor_set_tag(x_77, 7);
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_77, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_58);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_59);
if (x_89 == 0)
{
return x_59;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_59, 0);
x_91 = lean_ctor_get(x_59, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_59);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_55);
if (x_93 == 0)
{
return x_55;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_55, 0);
x_95 = lean_ctor_get(x_55, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_55);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
case 2:
{
lean_object* x_97; 
lean_dec(x_7);
lean_inc(x_1);
x_97 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_unsigned_to_nat(0u);
x_100 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_99);
lean_inc(x_1);
x_101 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_126; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
lean_dec(x_101);
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
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
x_126 = lean_unbox(x_108);
if (x_126 == 0)
{
lean_object* x_127; 
x_127 = lean_array_get_size(x_6);
x_110 = x_127;
goto block_125;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_array_get_size(x_6);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_sub(x_128, x_129);
lean_dec(x_128);
x_110 = x_130;
goto block_125;
}
block_125:
{
uint8_t x_111; 
x_111 = lean_nat_dec_lt(x_107, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; lean_object* x_114; 
lean_dec(x_109);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = lean_unbox(x_108);
lean_dec(x_108);
x_114 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_105, x_1, x_2, x_4, x_5, x_6, x_100, x_107, x_113, x_110, x_112, x_8, x_9, x_10, x_11, x_104);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_100);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_115 = l_Lean_MessageData_ofName(x_1);
x_116 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_109)) {
 x_117 = lean_alloc_ctor(7, 2, 0);
} else {
 x_117 = x_109;
 lean_ctor_set_tag(x_117, 7);
}
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_106)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_106;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_119, x_8, x_9, x_10, x_11, x_104);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_100);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_101);
if (x_131 == 0)
{
return x_101;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_101, 0);
x_133 = lean_ctor_get(x_101, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_101);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_97);
if (x_135 == 0)
{
return x_97;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_97, 0);
x_137 = lean_ctor_get(x_97, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_97);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
case 3:
{
lean_object* x_139; 
lean_dec(x_7);
lean_inc(x_1);
x_139 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_unsigned_to_nat(0u);
x_142 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_141);
lean_inc(x_1);
x_143 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_168; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_148 = x_144;
} else {
 lean_dec_ref(x_144);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_151 = x_145;
} else {
 lean_dec_ref(x_145);
 x_151 = lean_box(0);
}
x_168 = lean_unbox(x_150);
if (x_168 == 0)
{
lean_object* x_169; 
x_169 = lean_array_get_size(x_6);
x_152 = x_169;
goto block_167;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_array_get_size(x_6);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_sub(x_170, x_171);
lean_dec(x_170);
x_152 = x_172;
goto block_167;
}
block_167:
{
uint8_t x_153; 
x_153 = lean_nat_dec_lt(x_149, x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; 
lean_dec(x_151);
lean_dec(x_148);
x_154 = lean_box(0);
x_155 = lean_unbox(x_150);
lean_dec(x_150);
x_156 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_147, x_1, x_2, x_4, x_5, x_6, x_142, x_149, x_155, x_152, x_154, x_8, x_9, x_10, x_11, x_146);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_152);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_157 = l_Lean_MessageData_ofName(x_1);
x_158 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_151)) {
 x_159 = lean_alloc_ctor(7, 2, 0);
} else {
 x_159 = x_151;
 lean_ctor_set_tag(x_159, 7);
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_157);
x_160 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_148)) {
 x_161 = lean_alloc_ctor(7, 2, 0);
} else {
 x_161 = x_148;
 lean_ctor_set_tag(x_161, 7);
}
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_161, x_8, x_9, x_10, x_11, x_146);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_162);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_142);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = !lean_is_exclusive(x_143);
if (x_173 == 0)
{
return x_143;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_143, 0);
x_175 = lean_ctor_get(x_143, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_143);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_139);
if (x_177 == 0)
{
return x_139;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_139, 0);
x_179 = lean_ctor_get(x_139, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_139);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
case 4:
{
lean_object* x_181; 
lean_dec(x_7);
lean_inc(x_1);
x_181 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_183);
lean_inc(x_1);
x_185 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_182);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_210; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_185, 1);
lean_inc(x_188);
lean_dec(x_185);
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_190 = x_186;
} else {
 lean_dec_ref(x_186);
 x_190 = lean_box(0);
}
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_193 = x_187;
} else {
 lean_dec_ref(x_187);
 x_193 = lean_box(0);
}
x_210 = lean_unbox(x_192);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_array_get_size(x_6);
x_194 = x_211;
goto block_209;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_array_get_size(x_6);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_sub(x_212, x_213);
lean_dec(x_212);
x_194 = x_214;
goto block_209;
}
block_209:
{
uint8_t x_195; 
x_195 = lean_nat_dec_lt(x_191, x_194);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; 
lean_dec(x_193);
lean_dec(x_190);
x_196 = lean_box(0);
x_197 = lean_unbox(x_192);
lean_dec(x_192);
x_198 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_189, x_1, x_2, x_4, x_5, x_6, x_184, x_191, x_197, x_194, x_196, x_8, x_9, x_10, x_11, x_188);
return x_198;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_194);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_189);
lean_dec(x_184);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_199 = l_Lean_MessageData_ofName(x_1);
x_200 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_193)) {
 x_201 = lean_alloc_ctor(7, 2, 0);
} else {
 x_201 = x_193;
 lean_ctor_set_tag(x_201, 7);
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
x_202 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_190)) {
 x_203 = lean_alloc_ctor(7, 2, 0);
} else {
 x_203 = x_190;
 lean_ctor_set_tag(x_203, 7);
}
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_203, x_8, x_9, x_10, x_11, x_188);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
return x_204;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_204);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_184);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_185);
if (x_215 == 0)
{
return x_185;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_185, 0);
x_217 = lean_ctor_get(x_185, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_185);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
uint8_t x_219; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_219 = !lean_is_exclusive(x_181);
if (x_219 == 0)
{
return x_181;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_181, 0);
x_221 = lean_ctor_get(x_181, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_181);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
}
}
case 5:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_ctor_get(x_5, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_5, 1);
lean_inc(x_224);
lean_dec(x_5);
x_225 = lean_array_set(x_6, x_7, x_224);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_nat_sub(x_7, x_226);
lean_dec(x_7);
x_5 = x_223;
x_6 = x_225;
x_7 = x_227;
goto _start;
}
case 6:
{
lean_object* x_229; 
lean_dec(x_7);
lean_inc(x_1);
x_229 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = lean_unsigned_to_nat(0u);
x_232 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_231);
lean_inc(x_1);
x_233 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_258; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = lean_ctor_get(x_234, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_238 = x_234;
} else {
 lean_dec_ref(x_234);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_241 = x_235;
} else {
 lean_dec_ref(x_235);
 x_241 = lean_box(0);
}
x_258 = lean_unbox(x_240);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_array_get_size(x_6);
x_242 = x_259;
goto block_257;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_array_get_size(x_6);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_sub(x_260, x_261);
lean_dec(x_260);
x_242 = x_262;
goto block_257;
}
block_257:
{
uint8_t x_243; 
x_243 = lean_nat_dec_lt(x_239, x_242);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; lean_object* x_246; 
lean_dec(x_241);
lean_dec(x_238);
x_244 = lean_box(0);
x_245 = lean_unbox(x_240);
lean_dec(x_240);
x_246 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_237, x_1, x_2, x_4, x_5, x_6, x_232, x_239, x_245, x_242, x_244, x_8, x_9, x_10, x_11, x_236);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
lean_dec(x_242);
lean_dec(x_240);
lean_dec(x_239);
lean_dec(x_237);
lean_dec(x_232);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_247 = l_Lean_MessageData_ofName(x_1);
x_248 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_241)) {
 x_249 = lean_alloc_ctor(7, 2, 0);
} else {
 x_249 = x_241;
 lean_ctor_set_tag(x_249, 7);
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_238)) {
 x_251 = lean_alloc_ctor(7, 2, 0);
} else {
 x_251 = x_238;
 lean_ctor_set_tag(x_251, 7);
}
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_251, x_8, x_9, x_10, x_11, x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_253 = !lean_is_exclusive(x_252);
if (x_253 == 0)
{
return x_252;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_252, 0);
x_255 = lean_ctor_get(x_252, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_252);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
else
{
uint8_t x_263; 
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
x_263 = !lean_is_exclusive(x_233);
if (x_263 == 0)
{
return x_233;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_233, 0);
x_265 = lean_ctor_get(x_233, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_233);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_229);
if (x_267 == 0)
{
return x_229;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_229, 0);
x_269 = lean_ctor_get(x_229, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_229);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
case 7:
{
lean_object* x_271; 
lean_dec(x_7);
lean_inc(x_1);
x_271 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_unsigned_to_nat(0u);
x_274 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_273);
lean_inc(x_1);
x_275 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_272);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_300; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec(x_275);
x_279 = lean_ctor_get(x_276, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_280 = x_276;
} else {
 lean_dec_ref(x_276);
 x_280 = lean_box(0);
}
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_283 = x_277;
} else {
 lean_dec_ref(x_277);
 x_283 = lean_box(0);
}
x_300 = lean_unbox(x_282);
if (x_300 == 0)
{
lean_object* x_301; 
x_301 = lean_array_get_size(x_6);
x_284 = x_301;
goto block_299;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_array_get_size(x_6);
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_nat_sub(x_302, x_303);
lean_dec(x_302);
x_284 = x_304;
goto block_299;
}
block_299:
{
uint8_t x_285; 
x_285 = lean_nat_dec_lt(x_281, x_284);
if (x_285 == 0)
{
lean_object* x_286; uint8_t x_287; lean_object* x_288; 
lean_dec(x_283);
lean_dec(x_280);
x_286 = lean_box(0);
x_287 = lean_unbox(x_282);
lean_dec(x_282);
x_288 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_279, x_1, x_2, x_4, x_5, x_6, x_274, x_281, x_287, x_284, x_286, x_8, x_9, x_10, x_11, x_278);
return x_288;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
lean_dec(x_284);
lean_dec(x_282);
lean_dec(x_281);
lean_dec(x_279);
lean_dec(x_274);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_289 = l_Lean_MessageData_ofName(x_1);
x_290 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_283)) {
 x_291 = lean_alloc_ctor(7, 2, 0);
} else {
 x_291 = x_283;
 lean_ctor_set_tag(x_291, 7);
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_289);
x_292 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_280)) {
 x_293 = lean_alloc_ctor(7, 2, 0);
} else {
 x_293 = x_280;
 lean_ctor_set_tag(x_293, 7);
}
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_293, x_8, x_9, x_10, x_11, x_278);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
return x_294;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = lean_ctor_get(x_294, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_294);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_274);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_305 = !lean_is_exclusive(x_275);
if (x_305 == 0)
{
return x_275;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_275, 0);
x_307 = lean_ctor_get(x_275, 1);
lean_inc(x_307);
lean_inc(x_306);
lean_dec(x_275);
x_308 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
return x_308;
}
}
}
else
{
uint8_t x_309; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = !lean_is_exclusive(x_271);
if (x_309 == 0)
{
return x_271;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_271, 0);
x_311 = lean_ctor_get(x_271, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_271);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
}
case 8:
{
lean_object* x_313; 
lean_dec(x_7);
lean_inc(x_1);
x_313 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = lean_unsigned_to_nat(0u);
x_316 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_315);
lean_inc(x_1);
x_317 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_314);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_342; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_322 = x_318;
} else {
 lean_dec_ref(x_318);
 x_322 = lean_box(0);
}
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_319, 1);
lean_inc(x_324);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_325 = x_319;
} else {
 lean_dec_ref(x_319);
 x_325 = lean_box(0);
}
x_342 = lean_unbox(x_324);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_array_get_size(x_6);
x_326 = x_343;
goto block_341;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_array_get_size(x_6);
x_345 = lean_unsigned_to_nat(1u);
x_346 = lean_nat_sub(x_344, x_345);
lean_dec(x_344);
x_326 = x_346;
goto block_341;
}
block_341:
{
uint8_t x_327; 
x_327 = lean_nat_dec_lt(x_323, x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; lean_object* x_330; 
lean_dec(x_325);
lean_dec(x_322);
x_328 = lean_box(0);
x_329 = lean_unbox(x_324);
lean_dec(x_324);
x_330 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_321, x_1, x_2, x_4, x_5, x_6, x_316, x_323, x_329, x_326, x_328, x_8, x_9, x_10, x_11, x_320);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_dec(x_326);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_321);
lean_dec(x_316);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_331 = l_Lean_MessageData_ofName(x_1);
x_332 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_325)) {
 x_333 = lean_alloc_ctor(7, 2, 0);
} else {
 x_333 = x_325;
 lean_ctor_set_tag(x_333, 7);
}
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_322)) {
 x_335 = lean_alloc_ctor(7, 2, 0);
} else {
 x_335 = x_322;
 lean_ctor_set_tag(x_335, 7);
}
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_335, x_8, x_9, x_10, x_11, x_320);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_337 = !lean_is_exclusive(x_336);
if (x_337 == 0)
{
return x_336;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_336, 0);
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_336);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_316);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_347 = !lean_is_exclusive(x_317);
if (x_347 == 0)
{
return x_317;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_317, 0);
x_349 = lean_ctor_get(x_317, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_317);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
uint8_t x_351; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_351 = !lean_is_exclusive(x_313);
if (x_351 == 0)
{
return x_313;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_313, 0);
x_353 = lean_ctor_get(x_313, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_313);
x_354 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
return x_354;
}
}
}
case 9:
{
lean_object* x_355; 
lean_dec(x_7);
lean_inc(x_1);
x_355 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_355, 1);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_unsigned_to_nat(0u);
x_358 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_357);
lean_inc(x_1);
x_359 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_356);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_384; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_360, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
lean_dec(x_359);
x_363 = lean_ctor_get(x_360, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_364 = x_360;
} else {
 lean_dec_ref(x_360);
 x_364 = lean_box(0);
}
x_365 = lean_ctor_get(x_361, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_361, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_367 = x_361;
} else {
 lean_dec_ref(x_361);
 x_367 = lean_box(0);
}
x_384 = lean_unbox(x_366);
if (x_384 == 0)
{
lean_object* x_385; 
x_385 = lean_array_get_size(x_6);
x_368 = x_385;
goto block_383;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_array_get_size(x_6);
x_387 = lean_unsigned_to_nat(1u);
x_388 = lean_nat_sub(x_386, x_387);
lean_dec(x_386);
x_368 = x_388;
goto block_383;
}
block_383:
{
uint8_t x_369; 
x_369 = lean_nat_dec_lt(x_365, x_368);
if (x_369 == 0)
{
lean_object* x_370; uint8_t x_371; lean_object* x_372; 
lean_dec(x_367);
lean_dec(x_364);
x_370 = lean_box(0);
x_371 = lean_unbox(x_366);
lean_dec(x_366);
x_372 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_363, x_1, x_2, x_4, x_5, x_6, x_358, x_365, x_371, x_368, x_370, x_8, x_9, x_10, x_11, x_362);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec(x_368);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_358);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_373 = l_Lean_MessageData_ofName(x_1);
x_374 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_367)) {
 x_375 = lean_alloc_ctor(7, 2, 0);
} else {
 x_375 = x_367;
 lean_ctor_set_tag(x_375, 7);
}
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
x_376 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_364)) {
 x_377 = lean_alloc_ctor(7, 2, 0);
} else {
 x_377 = x_364;
 lean_ctor_set_tag(x_377, 7);
}
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_377, x_8, x_9, x_10, x_11, x_362);
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
lean_dec(x_358);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_359);
if (x_389 == 0)
{
return x_359;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_359, 0);
x_391 = lean_ctor_get(x_359, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_359);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_355);
if (x_393 == 0)
{
return x_355;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_355, 0);
x_395 = lean_ctor_get(x_355, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_355);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
case 10:
{
lean_object* x_397; 
lean_dec(x_7);
lean_inc(x_1);
x_397 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_unsigned_to_nat(0u);
x_400 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_399);
lean_inc(x_1);
x_401 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_398);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; uint8_t x_426; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_401, 1);
lean_inc(x_404);
lean_dec(x_401);
x_405 = lean_ctor_get(x_402, 0);
lean_inc(x_405);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_406 = x_402;
} else {
 lean_dec_ref(x_402);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_403, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_403, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_409 = x_403;
} else {
 lean_dec_ref(x_403);
 x_409 = lean_box(0);
}
x_426 = lean_unbox(x_408);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_array_get_size(x_6);
x_410 = x_427;
goto block_425;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_428 = lean_array_get_size(x_6);
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_nat_sub(x_428, x_429);
lean_dec(x_428);
x_410 = x_430;
goto block_425;
}
block_425:
{
uint8_t x_411; 
x_411 = lean_nat_dec_lt(x_407, x_410);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; lean_object* x_414; 
lean_dec(x_409);
lean_dec(x_406);
x_412 = lean_box(0);
x_413 = lean_unbox(x_408);
lean_dec(x_408);
x_414 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_405, x_1, x_2, x_4, x_5, x_6, x_400, x_407, x_413, x_410, x_412, x_8, x_9, x_10, x_11, x_404);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
lean_dec(x_410);
lean_dec(x_408);
lean_dec(x_407);
lean_dec(x_405);
lean_dec(x_400);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_415 = l_Lean_MessageData_ofName(x_1);
x_416 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_409)) {
 x_417 = lean_alloc_ctor(7, 2, 0);
} else {
 x_417 = x_409;
 lean_ctor_set_tag(x_417, 7);
}
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_415);
x_418 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_406)) {
 x_419 = lean_alloc_ctor(7, 2, 0);
} else {
 x_419 = x_406;
 lean_ctor_set_tag(x_419, 7);
}
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_419, x_8, x_9, x_10, x_11, x_404);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
return x_420;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_420, 0);
x_423 = lean_ctor_get(x_420, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_420);
x_424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
}
else
{
uint8_t x_431; 
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
x_431 = !lean_is_exclusive(x_401);
if (x_431 == 0)
{
return x_401;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_401, 0);
x_433 = lean_ctor_get(x_401, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_401);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
else
{
uint8_t x_435; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_435 = !lean_is_exclusive(x_397);
if (x_435 == 0)
{
return x_397;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_397, 0);
x_437 = lean_ctor_get(x_397, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_397);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
}
}
}
default: 
{
lean_object* x_439; 
lean_dec(x_7);
lean_inc(x_1);
x_439 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive(x_1, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
lean_dec(x_439);
x_441 = lean_unsigned_to_nat(0u);
x_442 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getNumParams(x_4, x_5, x_441);
lean_inc(x_1);
x_443 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim(x_1, x_3, x_4, x_6, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_468; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
lean_dec(x_443);
x_447 = lean_ctor_get(x_444, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_448 = x_444;
} else {
 lean_dec_ref(x_444);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_445, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_451 = x_445;
} else {
 lean_dec_ref(x_445);
 x_451 = lean_box(0);
}
x_468 = lean_unbox(x_450);
if (x_468 == 0)
{
lean_object* x_469; 
x_469 = lean_array_get_size(x_6);
x_452 = x_469;
goto block_467;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_array_get_size(x_6);
x_471 = lean_unsigned_to_nat(1u);
x_472 = lean_nat_sub(x_470, x_471);
lean_dec(x_470);
x_452 = x_472;
goto block_467;
}
block_467:
{
uint8_t x_453; 
x_453 = lean_nat_dec_lt(x_449, x_452);
if (x_453 == 0)
{
lean_object* x_454; uint8_t x_455; lean_object* x_456; 
lean_dec(x_451);
lean_dec(x_448);
x_454 = lean_box(0);
x_455 = lean_unbox(x_450);
lean_dec(x_450);
x_456 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_447, x_1, x_2, x_4, x_5, x_6, x_442, x_449, x_455, x_452, x_454, x_8, x_9, x_10, x_11, x_446);
return x_456;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_452);
lean_dec(x_450);
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_442);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_457 = l_Lean_MessageData_ofName(x_1);
x_458 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2;
if (lean_is_scalar(x_451)) {
 x_459 = lean_alloc_ctor(7, 2, 0);
} else {
 x_459 = x_451;
 lean_ctor_set_tag(x_459, 7);
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
x_460 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2;
if (lean_is_scalar(x_448)) {
 x_461 = lean_alloc_ctor(7, 2, 0);
} else {
 x_461 = x_448;
 lean_ctor_set_tag(x_461, 7);
}
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___spec__4(x_461, x_8, x_9, x_10, x_11, x_446);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_463 = !lean_is_exclusive(x_462);
if (x_463 == 0)
{
return x_462;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_462, 0);
x_465 = lean_ctor_get(x_462, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_462);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
else
{
uint8_t x_473; 
lean_dec(x_442);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_473 = !lean_is_exclusive(x_443);
if (x_473 == 0)
{
return x_443;
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_474 = lean_ctor_get(x_443, 0);
x_475 = lean_ctor_get(x_443, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_443);
x_476 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_476, 0, x_474);
lean_ctor_set(x_476, 1, x_475);
return x_476;
}
}
}
else
{
uint8_t x_477; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_477 = !lean_is_exclusive(x_439);
if (x_477 == 0)
{
return x_439;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_439, 0);
x_479 = lean_ctor_get(x_439, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_439);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_5, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_14, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_ConstantInfo_type(x_9);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___lambda__1), 10, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_9);
lean_closure_set(x_15, 2, x_12);
x_16 = 0;
x_17 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_14, x_15, x_16, x_3, x_4, x_5, x_6, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1___boxed(lean_object** _args) {
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
x_22 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
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
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___boxed(lean_object** _args) {
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
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 5);
x_8 = l_Lean_replaceRef(x_1, x_7);
lean_dec(x_7);
lean_ctor_set(x_3, 5, x_8);
x_9 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
x_13 = lean_ctor_get(x_3, 3);
x_14 = lean_ctor_get(x_3, 4);
x_15 = lean_ctor_get(x_3, 5);
x_16 = lean_ctor_get(x_3, 6);
x_17 = lean_ctor_get(x_3, 7);
x_18 = lean_ctor_get(x_3, 8);
x_19 = lean_ctor_get(x_3, 9);
x_20 = lean_ctor_get(x_3, 10);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*12);
x_22 = lean_ctor_get(x_3, 11);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*12 + 1);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_24 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
lean_ctor_set(x_25, 2, x_12);
lean_ctor_set(x_25, 3, x_13);
lean_ctor_set(x_25, 4, x_14);
lean_ctor_set(x_25, 5, x_24);
lean_ctor_set(x_25, 6, x_16);
lean_ctor_set(x_25, 7, x_17);
lean_ctor_set(x_25, 8, x_18);
lean_ctor_set(x_25, 9, x_19);
lean_ctor_set(x_25, 10, x_20);
lean_ctor_set(x_25, 11, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*12, x_21);
lean_ctor_set_uint8(x_25, sizeof(void*)*12 + 1, x_23);
x_26 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__1(x_2, x_25, x_4, x_5);
lean_dec(x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_sub(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1;
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Attr", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursor", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1;
x_2 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2;
x_3 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3;
x_4 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected attribute argument, numeral expected", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("major premise position must be greater than zero", 48, 48);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_1);
x_5 = l_Lean_Syntax_getKind(x_1);
x_6 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5;
x_7 = lean_name_eq(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7;
x_9 = l_Lean_throwErrorAt___at_Lean_getAttrParamOptPrio___spec__1(x_1, x_8, x_2, x_3, x_4);
lean_dec(x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_isNatLit_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10;
x_14 = l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1(x_1, x_13, x_2, x_3, x_4);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2(x_19, x_22, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_19);
x_24 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10;
x_25 = l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1(x_1, x_24, x_2, x_3, x_4);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwErrorAt___at_Lean_Meta_Attribute_Recursor_getMajorPos___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Attribute_Recursor_getMajorPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Attribute_Recursor_getMajorPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Attribute_Recursor_getMajorPos(x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__2;
x_5 = 0;
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8;
x_7 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7;
x_5 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13;
x_8 = lean_st_mk_ref(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9;
lean_inc(x_9);
x_12 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(x_1, x_6, x_11, x_9, x_3, x_4, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursorAttribute", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("user defined recursor, numerical parameter specifies position of the major premise", 82, 82);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5;
x_4 = 0;
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10;
x_3 = l_Lean_registerParametricAttribute___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__3(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_getMajorPos_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_recursorAttribute;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getMajorPos_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_instInhabitedNat;
x_4 = l_Lean_Meta_getMajorPos_x3f___closed__1;
x_5 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkRecursorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_st_ref_get(x_6, x_7);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_instInhabitedNat;
x_13 = l_Lean_Meta_getMajorPos_x3f___closed__1;
lean_inc(x_1);
x_14 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_12, x_13, x_11, x_1);
x_15 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(x_1, x_14, x_3, x_4, x_5, x_6, x_10);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(x_1, x_2, x_3, x_4, x_5, x_6, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore(x_1, x_20, x_3, x_4, x_5, x_6, x_16);
return x_21;
}
}
}
}
lean_object* initialize_Lean_AuxRecursor(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_RecursorInfo(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AuxRecursor(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1 = _init_l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1();
lean_mark_persistent(l_Lean_Meta_instToStringRecursorUnivLevelPos___closed__1);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__2___closed__1);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__1);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__2);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__3);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__4);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__1___closed__5);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__1);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__2);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__4___closed__3);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__1);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__3___closed__2);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__1);
l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2 = _init_l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2();
lean_mark_persistent(l_List_foldl___at_Lean_Meta_RecursorInfo_instToString___spec__8___closed__2);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__1);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__2);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__3);
l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4 = _init_l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4();
lean_mark_persistent(l_List_toString___at_Lean_Meta_RecursorInfo_instToString___spec__7___closed__4);
l_Lean_Meta_RecursorInfo_instToString___closed__1 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__1();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__1);
l_Lean_Meta_RecursorInfo_instToString___closed__2 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__2();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__2);
l_Lean_Meta_RecursorInfo_instToString___closed__3 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__3();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__3);
l_Lean_Meta_RecursorInfo_instToString___closed__4 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__4();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__4);
l_Lean_Meta_RecursorInfo_instToString___closed__5 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__5();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__5);
l_Lean_Meta_RecursorInfo_instToString___closed__6 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__6();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__6);
l_Lean_Meta_RecursorInfo_instToString___closed__7 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__7();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__7);
l_Lean_Meta_RecursorInfo_instToString___closed__8 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__8();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__8);
l_Lean_Meta_RecursorInfo_instToString___closed__9 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__9();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__9);
l_Lean_Meta_RecursorInfo_instToString___closed__10 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__10();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__10);
l_Lean_Meta_RecursorInfo_instToString___closed__11 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__11();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__11);
l_Lean_Meta_RecursorInfo_instToString___closed__12 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__12();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__12);
l_Lean_Meta_RecursorInfo_instToString___closed__13 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__13();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__13);
l_Lean_Meta_RecursorInfo_instToString___closed__14 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__14();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__14);
l_Lean_Meta_RecursorInfo_instToString___closed__15 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__15();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__15);
l_Lean_Meta_RecursorInfo_instToString___closed__16 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__16();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__16);
l_Lean_Meta_RecursorInfo_instToString___closed__17 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__17();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__17);
l_Lean_Meta_RecursorInfo_instToString___closed__18 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__18();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__18);
l_Lean_Meta_RecursorInfo_instToString___closed__19 = _init_l_Lean_Meta_RecursorInfo_instToString___closed__19();
lean_mark_persistent(l_Lean_Meta_RecursorInfo_instToString___closed__19);
l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1 = _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__1);
l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2 = _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__2);
l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3 = _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__3);
l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4 = _init_l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfoRec___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___spec__1___closed__4);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosIfAuxRecursor_x3f___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__2);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__3);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotive___closed__4);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___lambda__1___closed__2);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__2);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__3);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__4);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__5);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__6);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__7);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMajorPosDepElim___closed__8);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___spec__2___closed__3);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getParamsPos___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__1);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getIndicesPos___spec__2___closed__2);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getMotiveLevel___closed__2);
l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__1);
l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2 = _init_l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getUnivLevelPos___spec__1___closed__2);
l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1 = _init_l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_x27_loop___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___spec__3___lambda__1___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_getProduceMotiveAndRecursive___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__1);
l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2 = _init_l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2();
lean_mark_persistent(l___private_Lean_Meta_RecursorInfo_0__Lean_Meta_checkMotiveResultType___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__2___closed__2);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__1);
l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoCore___spec__3___closed__2);
l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___lambda__1___closed__1);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__1);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__2);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__3);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__4);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__5);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__6);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__7);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__8);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__9);
l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10 = _init_l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10();
lean_mark_persistent(l_Lean_Meta_Attribute_Recursor_getMajorPos___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__2();
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__10);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__11);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__12);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____lambda__2___closed__13);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__9);
l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806____closed__10);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_RecursorInfo___hyg_2806_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_recursorAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_recursorAttribute);
lean_dec_ref(res);
}l_Lean_Meta_getMajorPos_x3f___closed__1 = _init_l_Lean_Meta_getMajorPos_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_getMajorPos_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
