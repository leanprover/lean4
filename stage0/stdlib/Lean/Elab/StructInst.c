// Lean compiler output
// Module: Lean.Elab.StructInst
// Imports: Init Lean.Util.FindExpr Lean.Parser.Term Lean.Meta.Structure Lean.Elab.App Lean.Elab.Binders
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
static lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13;
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__6;
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8;
size_t lean_usize_add(size_t, size_t);
lean_object* l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_expr_x3f___default;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_addTermInfo_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1;
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9;
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo_x3f(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3(lean_object*);
lean_object* l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_params___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToFormatStruct;
lean_object* l_Lean_Syntax_mkSep(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT uint8_t l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4;
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1;
LEAN_EXPORT lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
lean_object* l_Lean_Expr_getAutoParamTactic_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2;
lean_object* l_Std_Format_joinSep___at_Prod_repr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__1(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_12069_(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1;
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3;
lean_object* l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4;
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6;
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5;
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3;
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedStruct;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2;
lean_object* l_Nat_max(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange(lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1;
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instInhabitedTermElabM(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3;
extern lean_object* l_Lean_levelZero;
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10;
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8;
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1;
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
lean_object* l_Lean_Core_withFreshMacroScope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1(lean_object*);
lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__5(lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5;
static lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
lean_object* lean_expr_consume_type_annotations(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3;
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_params(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToStringFieldStruct;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldStruct;
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6;
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default;
lean_object* l_Lean_Elab_Term_withMacroExpansion___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object*);
lean_object* l_Lean_Syntax_isFieldIdx_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatStruct___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___boxed(lean_object*);
static lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString(lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2;
lean_object* l_List_findSome_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15;
lean_object* lean_format_pretty(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1;
extern lean_object* l_Lean_Elab_abortTermExceptionId;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2;
lean_object* lean_array_to_list(lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___boxed(lean_object**);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2(lean_object*, lean_object*, uint8_t);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7;
static lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2;
lean_object* l_Lean_Meta_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3;
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5;
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
static lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1(lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_mkSepArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3;
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5;
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2;
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1;
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVarsFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
static lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_TSepArray_getElems___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(lean_object*);
uint8_t l_Lean_Syntax_isMissing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2;
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_findField_x3f___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Macro_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev(lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getSepArgs(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10;
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_instMonadTermElabM;
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
lean_object* lean_environment_main_module(lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12;
uint8_t l_Lean_Expr_isMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object*, lean_object*);
lean_object* l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2(size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7;
lean_object* l_Lean_getDefaultFnForField_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7;
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__2;
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1;
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1;
lean_object* l_Lean_Elab_Term_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4;
lean_object* l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2(size_t, size_t, lean_object*);
static lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6;
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6;
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2;
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6;
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1;
lean_object* l_Lean_Meta_getStructureName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6;
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4;
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5;
lean_object* l_Lean_Syntax_mkSynthetic(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
lean_object* l_Lean_Core_instantiateTypeLevelParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1;
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1;
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2;
static lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16;
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__1;
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default;
static lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__9;
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1___boxed(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3;
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1;
static lean_object* l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18;
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__4;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3;
static lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__5;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14;
static lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
static lean_object* l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default;
static lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3;
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
static lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9;
static lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11;
static lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__8;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7;
static lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedSource;
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_3 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscription", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4;
x_10 = l_Lean_Syntax_setArg(x_1, x_4, x_9);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_2, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13;
lean_inc(x_13);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16;
lean_inc(x_13);
x_17 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_19 = lean_array_push(x_18, x_17);
x_20 = lean_array_push(x_19, x_8);
x_21 = lean_box(2);
x_22 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15;
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
x_24 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_25 = lean_array_push(x_24, x_23);
x_26 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_array_push(x_18, x_10);
x_29 = lean_array_push(x_28, x_27);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_26);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19;
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_34 = lean_array_push(x_33, x_15);
x_35 = lean_array_push(x_34, x_30);
x_36 = lean_array_push(x_35, x_32);
x_37 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12;
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set(x_11, 0, x_38);
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13;
lean_inc(x_39);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16;
lean_inc(x_39);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_46 = lean_array_push(x_45, x_44);
x_47 = lean_array_push(x_46, x_8);
x_48 = lean_box(2);
x_49 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15;
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_47);
x_51 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_52 = lean_array_push(x_51, x_50);
x_53 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_52);
x_55 = lean_array_push(x_45, x_10);
x_56 = lean_array_push(x_55, x_54);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_53);
lean_ctor_set(x_57, 2, x_56);
x_58 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19;
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_61 = lean_array_push(x_60, x_42);
x_62 = lean_array_push(x_61, x_57);
x_63 = lean_array_push(x_62, x_59);
x_64 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12;
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_48);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_40);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(1);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_3);
return x_68;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInst", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Elab", 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("StructInst", 10);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandStructInstExpectedType", 28);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_macroAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
x_5 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Structure instances are of the form:\n\n      \"{\" >> optional (atomic (sepBy1 termParser \", \" >> \" with \"))\n          >> manyIndent (group ((structInstFieldAbbrev <|> structInstField) >> optional \", \"))\n          >> optEllipsis\n          >> optional (\" : \" >> termParser)\n          >> \" }\"\n", 288);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(35u);
x_2 = lean_unsigned_to_nat(28u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2;
x_4 = lean_unsigned_to_nat(28u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(28u);
x_2 = lean_unsigned_to_nat(76u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5;
x_4 = lean_unsigned_to_nat(76u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = lean_name_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ident", 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstLVal", 14);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_3 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":=", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_6, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_7, x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_7, x_6, x_13);
lean_inc(x_12);
x_15 = l_Lean_Syntax_isOfKind(x_12, x_2);
if (x_15 == 0)
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 1;
x_17 = lean_usize_add(x_6, x_16);
x_18 = lean_array_uset(x_14, x_6, x_12);
x_6 = x_17;
x_7 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Syntax_getArg(x_12, x_13);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2;
lean_inc(x_20);
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
size_t x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_6, x_23);
x_25 = lean_array_uset(x_14, x_6, x_12);
x_6 = x_24;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_12);
lean_inc(x_8);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3;
lean_inc(x_1);
x_31 = l_Lean_Name_str___override(x_1, x_30);
x_32 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
lean_inc(x_20);
x_33 = lean_array_push(x_32, x_20);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4;
x_35 = lean_array_push(x_33, x_34);
x_36 = lean_box(2);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_35);
x_38 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_28);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_41 = lean_array_push(x_40, x_37);
x_42 = lean_array_push(x_41, x_39);
x_43 = lean_array_push(x_42, x_20);
lean_inc(x_3);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_43);
x_45 = 1;
x_46 = lean_usize_add(x_6, x_45);
x_47 = lean_array_uset(x_14, x_6, x_44);
x_6 = x_46;
x_7 = x_47;
x_9 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_11 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstFieldAbbrev", 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstField", 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("{", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(",", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("}", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(6u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_2 = l_Array_append___rarg(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(2);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_3 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8;
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("..", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with", 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1;
lean_inc(x_1);
x_12 = l_Lean_Name_str___override(x_1, x_11);
x_13 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2;
lean_inc(x_1);
x_14 = l_Lean_Name_str___override(x_1, x_13);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_16);
lean_inc(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Syntax_getArgs(x_2);
x_19 = l_Lean_Syntax_TSepArray_getElems___rarg(x_18);
lean_dec(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_20, x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_26 = lean_box(1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
return x_27;
}
else
{
size_t x_28; size_t x_29; uint8_t x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1(x_12, x_19, x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = lean_box(1);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_10);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_inc(x_9);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2(x_1, x_12, x_14, x_16, x_29, x_28, x_19, x_9, x_10);
lean_dec(x_16);
lean_dec(x_12);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_MonadRef_mkInfoFromRefPos___at___aux__Init__Notation______macroRules__precMax__1___spec__1(x_9, x_35);
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
x_40 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3;
lean_inc(x_37);
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_get_size(x_34);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3(x_17, x_43, x_28, x_34);
lean_dec(x_17);
x_45 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5;
x_46 = l_Lean_mkSepArray(x_44, x_45);
lean_dec(x_44);
x_47 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_48 = l_Array_append___rarg(x_47, x_46);
x_49 = lean_box(2);
x_50 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_51 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_48);
x_52 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6;
lean_inc(x_37);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7;
x_55 = lean_array_push(x_54, x_41);
if (lean_obj_tag(x_6) == 0)
{
x_56 = x_47;
goto block_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_6, 0);
lean_inc(x_98);
lean_dec(x_6);
x_99 = l_Array_append___rarg(x_47, x_98);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_49);
lean_ctor_set(x_100, 1, x_50);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11;
lean_inc(x_37);
x_102 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_102, 0, x_37);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_104 = lean_array_push(x_103, x_100);
x_105 = lean_array_push(x_104, x_102);
x_56 = x_105;
goto block_97;
}
block_97:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = l_Array_append___rarg(x_47, x_56);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_49);
lean_ctor_set(x_58, 1, x_50);
lean_ctor_set(x_58, 2, x_57);
x_59 = lean_array_push(x_55, x_58);
x_60 = lean_array_push(x_59, x_51);
if (lean_obj_tag(x_5) == 0)
{
x_61 = x_47;
goto block_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_5, 0);
x_87 = l_Lean_Syntax_getHeadInfo_x3f(x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10;
lean_inc(x_37);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_37);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_91 = lean_array_push(x_90, x_89);
x_61 = x_91;
goto block_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10;
x_94 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_96 = lean_array_push(x_95, x_94);
x_61 = x_96;
goto block_85;
}
}
block_85:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = l_Array_append___rarg(x_47, x_61);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_65 = lean_array_push(x_64, x_63);
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_49);
lean_ctor_set(x_66, 1, x_3);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_array_push(x_60, x_66);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_37);
x_68 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_array_push(x_69, x_53);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_49);
lean_ctor_set(x_71, 1, x_4);
lean_ctor_set(x_71, 2, x_70);
if (lean_is_scalar(x_39)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_39;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_38);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_8, 0);
lean_inc(x_73);
lean_dec(x_8);
x_74 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16;
x_75 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_75, 0, x_37);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_77 = lean_array_push(x_76, x_75);
x_78 = lean_array_push(x_77, x_73);
x_79 = l_Array_append___rarg(x_47, x_78);
x_80 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_80, 0, x_49);
lean_ctor_set(x_80, 1, x_50);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_array_push(x_67, x_80);
x_82 = lean_array_push(x_81, x_53);
x_83 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_83, 0, x_49);
lean_ctor_set(x_83, 1, x_4);
lean_ctor_set(x_83, 2, x_82);
if (lean_is_scalar(x_39)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_39;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_38);
return x_84;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_13 = l_Lean_Syntax_isNone(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(2u);
lean_inc(x_12);
x_15 = l_Lean_Syntax_matchesNull(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_12, x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1(x_2, x_3, x_4, x_5, x_8, x_6, x_21, x_20, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1(x_2, x_3, x_4, x_5, x_8, x_6, x_24, x_23, x_9, x_10);
lean_dec(x_8);
lean_dec(x_3);
return x_25;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("optEllipsis", 11);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1;
lean_inc(x_2);
x_13 = l_Lean_Name_str___override(x_2, x_12);
lean_inc(x_11);
x_14 = l_Lean_Syntax_isOfKind(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_11, x_17);
lean_dec(x_11);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_18);
x_21 = l_Lean_Syntax_matchesNull(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lean_Syntax_getArg(x_18, x_17);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__2(x_1, x_2, x_9, x_13, x_3, x_5, x_26, x_25, x_6, x_7);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_18);
x_28 = lean_box(0);
x_29 = lean_box(0);
x_30 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__2(x_1, x_2, x_9, x_13, x_3, x_5, x_29, x_28, x_6, x_7);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_1, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_9);
x_12 = l_Lean_Syntax_matchesNull(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_9, x_15);
lean_dec(x_9);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3(x_1, x_19, x_4, x_20, x_18, x_2, x_3);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_24 = lean_box(0);
x_25 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3(x_1, x_23, x_4, x_24, x_22, x_2, x_3);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2(x_1, x_2, x_3, x_4, x_10, x_11, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expandStructInstFieldAbbrev", 27);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Expand field abbreviations. Example: `{ x, y := 0 }` expands to `{ x := x, y := 0 }` ", 85);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = lean_unsigned_to_nat(44u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = lean_unsigned_to_nat(31u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1;
x_2 = lean_unsigned_to_nat(44u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2;
x_4 = lean_unsigned_to_nat(31u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(38u);
x_2 = lean_unsigned_to_nat(75u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4;
x_2 = lean_unsigned_to_nat(48u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5;
x_4 = lean_unsigned_to_nat(75u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("src", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("let", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letDecl", 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letIdDecl", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(";", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_9);
x_12 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_9, 10);
lean_inc(x_15);
x_16 = lean_st_ref_get(x_10, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_environment_main_module(x_19);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4;
lean_inc(x_15);
x_22 = l_Lean_addMacroScope(x_20, x_21, x_15);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3;
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
x_26 = lean_array_push(x_1, x_25);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go(x_2, x_3, x_26, x_4, x_5, x_6, x_7, x_9, x_10, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_9, x_10, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_10, x_32);
lean_dec(x_10);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_environment_main_module(x_36);
x_38 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5;
lean_inc(x_31);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addMacroScope(x_37, x_21, x_15);
lean_inc(x_31);
x_41 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_24);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set(x_41, 3, x_23);
x_42 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
lean_inc(x_31);
x_43 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11;
x_45 = lean_array_push(x_44, x_41);
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4;
x_47 = lean_array_push(x_45, x_46);
x_48 = lean_array_push(x_47, x_46);
x_49 = lean_array_push(x_48, x_43);
x_50 = lean_array_push(x_49, x_8);
x_51 = lean_box(2);
x_52 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10;
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_50);
x_54 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8;
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_55);
x_58 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12;
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_31);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13;
x_61 = lean_array_push(x_60, x_39);
x_62 = lean_array_push(x_61, x_57);
x_63 = lean_array_push(x_62, x_59);
x_64 = lean_array_push(x_63, x_28);
x_65 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6;
x_66 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_64);
lean_ctor_set(x_33, 0, x_66);
return x_33;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_67 = lean_ctor_get(x_33, 0);
x_68 = lean_ctor_get(x_33, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_33);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_environment_main_module(x_69);
x_71 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5;
lean_inc(x_31);
x_72 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_72, 0, x_31);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_addMacroScope(x_70, x_21, x_15);
lean_inc(x_31);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_31);
lean_ctor_set(x_74, 1, x_24);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_23);
x_75 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
lean_inc(x_31);
x_76 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_76, 0, x_31);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11;
x_78 = lean_array_push(x_77, x_74);
x_79 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4;
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_array_push(x_80, x_79);
x_82 = lean_array_push(x_81, x_76);
x_83 = lean_array_push(x_82, x_8);
x_84 = lean_box(2);
x_85 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10;
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_83);
x_87 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_88 = lean_array_push(x_87, x_86);
x_89 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8;
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_88);
x_91 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12;
x_92 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_92, 0, x_31);
lean_ctor_set(x_92, 1, x_91);
x_93 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13;
x_94 = lean_array_push(x_93, x_72);
x_95 = lean_array_push(x_94, x_90);
x_96 = lean_array_push(x_95, x_92);
x_97 = lean_array_push(x_96, x_28);
x_98 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6;
x_99 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_99, 0, x_84);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_99, 2, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_68);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_101 = !lean_is_exclusive(x_27);
if (x_101 == 0)
{
return x_27;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_27, 0);
x_103 = lean_ctor_get(x_27, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_27);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", ", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
lean_inc(x_1);
x_12 = l_Lean_mkAtomFrom(x_1, x_11);
x_13 = l_Lean_Syntax_mkSep(x_3, x_12);
lean_dec(x_3);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_1, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_setArg(x_15, x_16, x_13);
x_18 = l_Lean_Syntax_setArg(x_1, x_14, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_20);
x_22 = l_Lean_Elab_Term_isLocalIdent_x3f(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1), 11, 8);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_1);
lean_closure_set(x_25, 2, x_21);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_7);
lean_closure_set(x_25, 7, x_20);
x_26 = l_Lean_Core_withFreshMacroScope___rarg(x_25, x_8, x_9, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_array_push(x_3, x_20);
x_2 = x_21;
x_3 = x_28;
x_10 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = l_Lean_Syntax_isMissing(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
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
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortTermExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_isLocalIdent_x3f(x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
lean_dec(x_14);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_10 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_27 = 0;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_10);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_array_to_list(lean_box(0), x_1);
x_12 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go(x_2, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
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
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_17);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_dec(x_5);
if (x_3 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_4, x_4);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(x_1, x_2, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
else
{
size_t x_18; size_t x_19; uint8_t x_20; 
x_18 = 0;
x_19 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_20 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1(x_1, x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(x_1, x_2, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg(x_12);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
lean_dec(x_3);
x_11 = l_Lean_Syntax_getSepArgs(x_1);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_22; 
x_22 = 1;
x_15 = x_22;
x_16 = x_10;
goto block_21;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_12, x_12);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 1;
x_15 = x_24;
x_16 = x_10;
goto block_21;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_12);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_27 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3(x_11, x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = 1;
x_15 = x_31;
x_16 = x_30;
goto block_21;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = 0;
x_15 = x_33;
x_16 = x_32;
goto block_21;
}
}
}
block_21:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2(x_11, x_2, x_14, x_12, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_Syntax_isMissing(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__3(x_13, x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg(x_8);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__3(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___lambda__2(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedSource() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Source_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("with ", 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_6 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_5);
x_7 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
lean_inc(x_6);
x_8 = l_Lean_mkAtomFrom(x_6, x_7);
x_9 = l_Lean_Syntax_mkSep(x_1, x_8);
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5;
x_11 = l_Lean_mkAtomFrom(x_6, x_10);
x_12 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_13 = lean_array_push(x_12, x_9);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_box(2);
x_16 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_array_fget(x_1, x_3);
x_19 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
lean_inc(x_18);
x_20 = l_Lean_mkAtomFrom(x_18, x_19);
x_21 = l_Lean_Syntax_mkSep(x_1, x_20);
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5;
x_23 = l_Lean_mkAtomFrom(x_18, x_22);
x_24 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_25 = lean_array_push(x_24, x_21);
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_box(2);
x_28 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_instInhabitedTermElabM(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.StructInst", 20);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.getStructSource", 73);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2;
x_3 = lean_unsigned_to_nat(115u);
x_4 = lean_unsigned_to_nat(43u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_13);
x_23 = l_Lean_Elab_Term_isLocalIdent_x3f(x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2(x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_16 = x_28;
x_17 = x_29;
goto block_22;
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_box(0);
x_37 = lean_box(0);
x_38 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_35);
lean_inc(x_13);
x_39 = l_Lean_Elab_Term_addTermInfo_x27(x_13, x_35, x_36, x_36, x_37, x_38, x_4, x_5, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = lean_infer_type(x_35, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = lean_whnf(x_42, x_6, x_7, x_8, x_9, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_45);
x_47 = l_Lean_Elab_Term_tryPostponeIfMVar(x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Meta_getStructureName(x_45, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_13);
lean_ctor_set(x_52, 1, x_50);
x_16 = x_52;
x_17 = x_51;
goto block_22;
}
else
{
uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
return x_49;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_49, 0);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_49);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_45);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_47);
if (x_57 == 0)
{
return x_47;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_47, 0);
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_47);
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
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_44);
if (x_61 == 0)
{
return x_44;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_44, 0);
x_63 = lean_ctor_get(x_44, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_44);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_41);
if (x_65 == 0)
{
return x_41;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_41, 0);
x_67 = lean_ctor_get(x_41, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_41);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_69 = !lean_is_exclusive(x_39);
if (x_69 == 0)
{
return x_39;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_39, 0);
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_39);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_22:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_19;
x_3 = x_20;
x_10 = x_17;
goto _start;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid structure instance `with` and `..` cannot be used together", 66);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 5);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_dec(x_1);
lean_ctor_set(x_6, 5, x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_19 = l_Lean_Syntax_isNone(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2;
x_21 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_22 = l_Lean_Syntax_getArg(x_10, x_17);
lean_dec(x_10);
x_23 = l_Lean_Syntax_getSepArgs(x_22);
lean_dec(x_22);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = 0;
x_27 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3(x_25, x_26, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
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
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_31);
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
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_39 = lean_ctor_get(x_6, 0);
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
x_44 = lean_ctor_get(x_6, 5);
x_45 = lean_ctor_get(x_6, 6);
x_46 = lean_ctor_get(x_6, 7);
x_47 = lean_ctor_get(x_6, 8);
x_48 = lean_ctor_get(x_6, 9);
x_49 = lean_ctor_get(x_6, 10);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_6);
x_50 = l_Lean_replaceRef(x_1, x_44);
lean_dec(x_44);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_40);
lean_ctor_set(x_51, 2, x_41);
lean_ctor_set(x_51, 3, x_42);
lean_ctor_set(x_51, 4, x_43);
lean_ctor_set(x_51, 5, x_50);
lean_ctor_set(x_51, 6, x_45);
lean_ctor_set(x_51, 7, x_46);
lean_ctor_set(x_51, 8, x_47);
lean_ctor_set(x_51, 9, x_48);
lean_ctor_set(x_51, 10, x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Lean_Syntax_getArg(x_12, x_52);
lean_dec(x_12);
x_54 = l_Lean_Syntax_isNone(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_10);
x_55 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2;
x_56 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(x_55, x_2, x_3, x_4, x_5, x_51, x_7, x_8);
lean_dec(x_7);
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_57 = l_Lean_Syntax_getArg(x_10, x_52);
lean_dec(x_10);
x_58 = l_Lean_Syntax_getSepArgs(x_57);
lean_dec(x_57);
x_59 = lean_array_get_size(x_58);
x_60 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_61 = 0;
x_62 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3(x_60, x_61, x_58, x_2, x_3, x_4, x_5, x_51, x_7, x_8);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_63);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_70 = x_62;
} else {
 lean_dec_ref(x_62);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Syntax_getArg(x_12, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_12);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_8);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_12);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_8);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_8);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstArrayRef", 18);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, can't mix field and `[..]` at a given level", 67);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, at most one `[..]` at a given level", 59);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_13);
x_14 = l_Lean_Syntax_getKind(x_13);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1;
x_16 = lean_name_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
size_t x_17; size_t x_18; 
lean_dec(x_13);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Syntax_getArg(x_13, x_20);
x_22 = l_Lean_Syntax_getArg(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_Syntax_getKind(x_22);
x_24 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_25 = lean_name_eq(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_26; size_t x_27; size_t x_28; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_13);
x_27 = 1;
x_28 = lean_usize_add(x_2, x_27);
x_2 = x_28;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_4, 0);
lean_inc(x_30);
x_31 = l_Lean_Syntax_getKind(x_30);
x_32 = lean_name_eq(x_31, x_24);
lean_dec(x_31);
if (x_32 == 0)
{
size_t x_33; size_t x_34; 
lean_dec(x_13);
x_33 = 1;
x_34 = lean_usize_add(x_2, x_33);
x_2 = x_34;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_4);
x_36 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5;
x_37 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_13, x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_42; size_t x_43; size_t x_44; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_13);
x_43 = 1;
x_44 = lean_usize_add(x_2, x_43);
x_2 = x_44;
x_4 = x_42;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_4, 0);
lean_inc(x_46);
lean_dec(x_4);
x_47 = l_Lean_Syntax_getKind(x_46);
x_48 = lean_name_eq(x_47, x_24);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5;
x_50 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_13, x_49, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7;
x_56 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_13, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_box(0);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_getSepArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = x_9;
x_11 = x_8;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = x_9;
x_11 = x_8;
goto block_22;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(x_25, x_30, x_31, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_10 = x_33;
x_11 = x_34;
goto block_22;
}
else
{
uint8_t x_35; 
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
block_22:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_17 = l_Lean_Syntax_getKind(x_16);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_19 = lean_name_eq(x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 1;
x_13 = lean_box(x_12);
x_14 = lean_box(x_12);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_13);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_3, x_1, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj", 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("modifyOp", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("namedArgument", 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("idx", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fun", 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("basicFun", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("=>", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n===>\n", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_1, x_22);
lean_dec(x_1);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_23, x_24);
lean_dec(x_23);
x_26 = lean_array_get_size(x_2);
x_27 = lean_nat_dec_lt(x_22, x_26);
lean_dec(x_26);
lean_inc(x_19);
x_28 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_19, x_20, x_21);
if (x_27 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_2);
x_140 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_141 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___spec__1(x_140);
x_29 = x_141;
goto block_139;
}
else
{
lean_object* x_142; 
x_142 = lean_array_fget(x_2, x_22);
lean_dec(x_2);
x_29 = x_142;
goto block_139;
}
block_139:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_19, 10);
lean_inc(x_33);
x_34 = lean_st_ref_get(x_20, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_environment_main_module(x_37);
x_39 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1;
lean_inc(x_3);
x_40 = l_Lean_Name_str___override(x_3, x_39);
x_41 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2;
lean_inc(x_3);
x_42 = l_Lean_Name_str___override(x_3, x_41);
x_43 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
lean_inc(x_30);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_30);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7;
lean_inc(x_33);
lean_inc(x_38);
x_46 = l_Lean_addMacroScope(x_38, x_45, x_33);
x_47 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6;
lean_inc(x_4);
lean_inc(x_30);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_30);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
lean_ctor_set(x_48, 3, x_4);
x_49 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_50 = lean_array_push(x_49, x_32);
x_51 = lean_array_push(x_50, x_44);
x_52 = lean_array_push(x_51, x_48);
x_53 = lean_box(2);
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_52);
x_55 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8;
lean_inc(x_3);
x_56 = l_Lean_Name_str___override(x_3, x_55);
x_57 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13;
lean_inc(x_30);
x_58 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_58, 0, x_30);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12;
lean_inc(x_33);
lean_inc(x_38);
x_60 = l_Lean_addMacroScope(x_38, x_59, x_33);
x_61 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11;
lean_inc(x_4);
lean_inc(x_30);
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_30);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_4);
x_63 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
lean_inc(x_30);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_30);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19;
lean_inc(x_30);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_30);
lean_ctor_set(x_66, 1, x_65);
x_67 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11;
lean_inc(x_58);
x_68 = lean_array_push(x_67, x_58);
x_69 = lean_array_push(x_68, x_62);
x_70 = lean_array_push(x_69, x_64);
x_71 = lean_array_push(x_70, x_25);
lean_inc(x_66);
x_72 = lean_array_push(x_71, x_66);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_73, 1, x_56);
lean_ctor_set(x_73, 2, x_72);
x_74 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11;
lean_inc(x_3);
x_75 = l_Lean_Name_str___override(x_3, x_74);
x_76 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13;
lean_inc(x_3);
x_77 = l_Lean_Name_str___override(x_3, x_76);
lean_inc(x_30);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_30);
lean_ctor_set(x_78, 1, x_76);
x_79 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14;
x_80 = l_Lean_Name_str___override(x_3, x_79);
x_81 = l_Lean_addMacroScope(x_38, x_5, x_33);
lean_inc(x_30);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_30);
lean_ctor_set(x_82, 1, x_6);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_4);
x_83 = lean_array_push(x_7, x_82);
lean_inc(x_8);
x_84 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_84, 0, x_53);
lean_ctor_set(x_84, 1, x_8);
lean_ctor_set(x_84, 2, x_83);
x_85 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_inc(x_8);
x_86 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_86, 0, x_53);
lean_ctor_set(x_86, 1, x_8);
lean_ctor_set(x_86, 2, x_85);
x_87 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15;
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_30);
lean_ctor_set(x_88, 1, x_87);
x_89 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13;
x_90 = lean_array_push(x_89, x_84);
lean_inc(x_86);
x_91 = lean_array_push(x_90, x_86);
x_92 = lean_array_push(x_91, x_88);
x_93 = lean_array_push(x_92, x_9);
x_94 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_94, 0, x_53);
lean_ctor_set(x_94, 1, x_80);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_10);
x_95 = lean_array_push(x_10, x_78);
x_96 = lean_array_push(x_95, x_94);
x_97 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_97, 0, x_53);
lean_ctor_set(x_97, 1, x_77);
lean_ctor_set(x_97, 2, x_96);
lean_inc(x_10);
x_98 = lean_array_push(x_10, x_97);
x_99 = lean_array_push(x_98, x_86);
lean_inc(x_8);
x_100 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_100, 0, x_53);
lean_ctor_set(x_100, 1, x_8);
lean_ctor_set(x_100, 2, x_99);
x_101 = lean_array_push(x_49, x_58);
x_102 = lean_array_push(x_101, x_100);
x_103 = lean_array_push(x_102, x_66);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_53);
lean_ctor_set(x_104, 1, x_75);
lean_ctor_set(x_104, 2, x_103);
lean_inc(x_10);
x_105 = lean_array_push(x_10, x_73);
x_106 = lean_array_push(x_105, x_104);
x_107 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_107, 0, x_53);
lean_ctor_set(x_107, 1, x_8);
lean_ctor_set(x_107, 2, x_106);
x_108 = lean_array_push(x_10, x_54);
x_109 = lean_array_push(x_108, x_107);
x_110 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_110, 0, x_53);
lean_ctor_set(x_110, 1, x_40);
lean_ctor_set(x_110, 2, x_109);
x_128 = lean_st_ref_get(x_20, x_36);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_129, 3);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_ctor_get_uint8(x_130, sizeof(void*)*1);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_dec(x_128);
x_133 = 0;
x_111 = x_133;
x_112 = x_132;
goto block_127;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
lean_inc(x_13);
x_135 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_13, x_15, x_16, x_17, x_18, x_19, x_20, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_unbox(x_136);
lean_dec(x_136);
x_111 = x_138;
x_112 = x_137;
goto block_127;
}
block_127:
{
if (x_111 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_13);
x_113 = lean_box(0);
x_114 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(x_110, x_11, x_12, x_113, x_15, x_16, x_17, x_18, x_19, x_20, x_112);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_inc(x_12);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_12);
x_116 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19;
x_119 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_110);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_110);
x_121 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_116);
x_123 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_13, x_122, x_15, x_16, x_17, x_18, x_19, x_20, x_112);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(x_110, x_11, x_12, x_124, x_15, x_16, x_17, x_18, x_19, x_20, x_125);
lean_dec(x_124);
return x_126;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("s", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("struct", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\nval: ", 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_10);
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_10, 10);
lean_inc(x_21);
x_22 = lean_st_ref_get(x_11, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_environment_main_module(x_25);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4;
x_28 = l_Lean_addMacroScope(x_26, x_27, x_21);
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = l_Lean_Syntax_getArg(x_16, x_13);
lean_inc(x_32);
x_33 = l_Lean_Syntax_getKind(x_32);
x_34 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_toSubarray___rarg(x_36, x_15, x_37);
x_39 = l_Array_ofSubarray___rarg(x_38);
x_40 = lean_box(2);
x_41 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_39);
x_43 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_44 = lean_array_push(x_43, x_31);
x_45 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax(x_44);
lean_dec(x_44);
lean_inc(x_2);
x_46 = l_Lean_Syntax_setArg(x_2, x_15, x_45);
x_47 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9;
x_48 = lean_st_ref_get(x_11, x_24);
if (x_35 == 0)
{
lean_object* x_90; 
x_90 = l_Lean_Syntax_getArg(x_32, x_15);
lean_dec(x_32);
x_49 = x_90;
goto block_89;
}
else
{
x_49 = x_32;
goto block_89;
}
block_89:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_50 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_51 = lean_array_push(x_50, x_49);
x_52 = lean_array_push(x_51, x_42);
x_53 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5;
x_54 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_52);
x_55 = l_Lean_Syntax_setArg(x_1, x_13, x_54);
x_56 = lean_array_push(x_43, x_55);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_41);
lean_ctor_set(x_57, 2, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = l_Lean_Syntax_setArg(x_46, x_58, x_57);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_79, 3);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_ctor_get_uint8(x_80, sizeof(void*)*1);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_48, 1);
lean_inc(x_82);
lean_dec(x_48);
x_83 = 0;
x_60 = x_83;
x_61 = x_82;
goto block_78;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_dec(x_48);
x_85 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_unbox(x_86);
lean_dec(x_86);
x_60 = x_88;
x_61 = x_87;
goto block_78;
}
block_78:
{
if (x_60 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_63 = lean_box(0);
x_64 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2(x_14, x_3, x_62, x_29, x_27, x_30, x_43, x_41, x_59, x_50, x_4, x_2, x_47, x_63, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_2);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_2);
x_66 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_59);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_59);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
x_73 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_47, x_72, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_77 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2(x_14, x_3, x_76, x_29, x_27, x_30, x_43, x_41, x_59, x_50, x_4, x_2, x_47, x_74, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
lean_dec(x_74);
return x_77;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
lean_dec(x_16);
x_91 = lean_unsigned_to_nat(2u);
x_92 = l_Lean_Syntax_getArg(x_1, x_91);
lean_dec(x_1);
x_93 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
x_94 = l_Lean_Syntax_getArg(x_93, x_15);
lean_dec(x_93);
x_95 = lean_array_get_size(x_3);
x_96 = lean_nat_dec_lt(x_13, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_3);
x_210 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_211 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___spec__1(x_210);
x_97 = x_211;
goto block_209;
}
else
{
lean_object* x_212; 
x_212 = lean_array_fget(x_3, x_13);
lean_dec(x_3);
x_97 = x_212;
goto block_209;
}
block_209:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_10);
x_99 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_10, x_11, x_12);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_ctor_get(x_10, 10);
lean_inc(x_102);
x_103 = lean_st_ref_get(x_11, x_101);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_environment_main_module(x_106);
x_108 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
lean_inc(x_100);
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_100);
lean_ctor_set(x_109, 1, x_108);
x_110 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7;
lean_inc(x_102);
lean_inc(x_107);
x_111 = l_Lean_addMacroScope(x_107, x_110, x_102);
x_112 = lean_box(0);
x_113 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6;
lean_inc(x_100);
x_114 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_112);
x_115 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_116 = lean_array_push(x_115, x_98);
x_117 = lean_array_push(x_116, x_109);
x_118 = lean_array_push(x_117, x_114);
x_119 = lean_box(2);
x_120 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13;
x_121 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_118);
x_122 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13;
lean_inc(x_100);
x_123 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_123, 0, x_100);
lean_ctor_set(x_123, 1, x_122);
x_124 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12;
lean_inc(x_102);
lean_inc(x_107);
x_125 = l_Lean_addMacroScope(x_107, x_124, x_102);
x_126 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11;
lean_inc(x_100);
x_127 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_127, 0, x_100);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_125);
lean_ctor_set(x_127, 3, x_112);
x_128 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5;
lean_inc(x_100);
x_129 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_129, 0, x_100);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19;
lean_inc(x_100);
x_131 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_131, 0, x_100);
lean_ctor_set(x_131, 1, x_130);
x_132 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11;
lean_inc(x_123);
x_133 = lean_array_push(x_132, x_123);
x_134 = lean_array_push(x_133, x_127);
x_135 = lean_array_push(x_134, x_129);
x_136 = lean_array_push(x_135, x_94);
lean_inc(x_131);
x_137 = lean_array_push(x_136, x_131);
x_138 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14;
x_139 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_139, 0, x_119);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_139, 2, x_137);
x_140 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13;
lean_inc(x_100);
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_100);
lean_ctor_set(x_141, 1, x_140);
x_142 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4;
x_143 = l_Lean_addMacroScope(x_107, x_142, x_102);
x_144 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3;
lean_inc(x_100);
x_145 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_145, 0, x_100);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_143);
lean_ctor_set(x_145, 3, x_112);
x_146 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18;
x_147 = lean_array_push(x_146, x_145);
x_148 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_149 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_149, 0, x_119);
lean_ctor_set(x_149, 1, x_148);
lean_ctor_set(x_149, 2, x_147);
x_150 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15;
x_151 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_151, 0, x_100);
lean_ctor_set(x_151, 1, x_150);
x_152 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13;
x_153 = lean_array_push(x_152, x_149);
x_154 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4;
x_155 = lean_array_push(x_153, x_154);
x_156 = lean_array_push(x_155, x_151);
x_157 = lean_array_push(x_156, x_92);
x_158 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16;
x_159 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_159, 0, x_119);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_159, 2, x_157);
x_160 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_161 = lean_array_push(x_160, x_141);
x_162 = lean_array_push(x_161, x_159);
x_163 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15;
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_119);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_164, 2, x_162);
x_165 = lean_array_push(x_160, x_164);
x_166 = lean_array_push(x_165, x_154);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_119);
lean_ctor_set(x_167, 1, x_148);
lean_ctor_set(x_167, 2, x_166);
x_168 = lean_array_push(x_115, x_123);
x_169 = lean_array_push(x_168, x_167);
x_170 = lean_array_push(x_169, x_131);
x_171 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12;
x_172 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_172, 0, x_119);
lean_ctor_set(x_172, 1, x_171);
lean_ctor_set(x_172, 2, x_170);
x_173 = lean_array_push(x_160, x_139);
x_174 = lean_array_push(x_173, x_172);
x_175 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_175, 0, x_119);
lean_ctor_set(x_175, 1, x_148);
lean_ctor_set(x_175, 2, x_174);
x_176 = lean_array_push(x_160, x_121);
x_177 = lean_array_push(x_176, x_175);
x_178 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12;
x_179 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_179, 0, x_119);
lean_ctor_set(x_179, 1, x_178);
lean_ctor_set(x_179, 2, x_177);
x_180 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9;
x_198 = lean_st_ref_get(x_11, x_105);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_199, 3);
lean_inc(x_200);
lean_dec(x_199);
x_201 = lean_ctor_get_uint8(x_200, sizeof(void*)*1);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
lean_dec(x_198);
x_203 = 0;
x_181 = x_203;
x_182 = x_202;
goto block_197;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_198, 1);
lean_inc(x_204);
lean_dec(x_198);
x_205 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_180, x_6, x_7, x_8, x_9, x_10, x_11, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = lean_unbox(x_206);
lean_dec(x_206);
x_181 = x_208;
x_182 = x_207;
goto block_197;
}
block_197:
{
if (x_181 == 0)
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_box(0);
x_184 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(x_179, x_4, x_2, x_183, x_6, x_7, x_8, x_9, x_10, x_11, x_182);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_inc(x_2);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_2);
x_186 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_187 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19;
x_189 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_179);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_179);
x_191 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_186);
x_193 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_180, x_192, x_6, x_7, x_8, x_9, x_10, x_11, x_182);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(x_179, x_4, x_2, x_194, x_6, x_7, x_8, x_9, x_10, x_11, x_195);
lean_dec(x_194);
return x_196;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, multiple sources and array update is not supported.", 75);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3(x_2, x_1, x_3, x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__4(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
_start:
{
lean_object* x_22; 
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_14);
return x_22;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, expected type is not known", 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, ", 24);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" type is not of the form (C ...)", 32);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_getAppFn(x_11);
x_14 = l_Lean_Expr_isMVar(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = l_Lean_stringToMessageData(x_2);
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_indentExpr(x_11);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_14 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___spec__1(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_1, x_11);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, expected type is not known, using the type of the first source, extra sources are not needed", 116);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("expected", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, structure type expected", 47);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_lt(x_14, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1(x_12, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_12);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_array_fget(x_12, x_14);
lean_dec(x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2;
x_21 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_dec(x_10);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_dec(x_10);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_29);
x_30 = lean_whnf(x_29, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_getAppFn(x_31);
if (lean_obj_tag(x_33) == 4)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_29);
lean_dec(x_2);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_st_ref_get(x_8, x_32);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_34);
x_40 = l_Lean_isStructure(x_39, x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_free_object(x_35);
lean_dec(x_34);
x_41 = l_Lean_indentExpr(x_31);
x_42 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__4(x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_35, 0);
x_52 = lean_ctor_get(x_35, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_35);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_34);
x_54 = l_Lean_isStructure(x_53, x_34);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_34);
x_55 = l_Lean_indentExpr(x_31);
x_56 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__4(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
else
{
lean_object* x_65; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_34);
lean_ctor_set(x_65, 1, x_52);
return x_65;
}
}
}
else
{
lean_dec(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_29);
x_66 = lean_ctor_get(x_2, 0);
lean_inc(x_66);
lean_dec(x_2);
x_67 = lean_array_get_size(x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_dec_lt(x_68, x_67);
lean_dec(x_67);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_box(0);
x_71 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1(x_66, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_66);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_72 = lean_array_fget(x_66, x_68);
lean_dec(x_66);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2;
x_75 = l_Lean_throwErrorAt___at___private_Lean_Elab_Binders_0__Lean_Elab_Term_elabBinderViews_loop___spec__1(x_73, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_73);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
return x_75;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_75);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_80 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3;
x_81 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_29, x_80, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_30);
if (x_82 == 0)
{
return x_30;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_30, 0);
x_84 = lean_ctor_get(x_30, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_30);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_10);
if (x_86 == 0)
{
return x_10;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_10, 0);
x_88 = lean_ctor_get(x_10, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_10);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = 1;
x_4 = l_Lean_Name_toString(x_2, x_3);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Nat_repr(x_6);
x_8 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Syntax_prettyPrint(x_9);
x_11 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1;
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_expr_x3f___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1;
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instInhabitedStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_params(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_params___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_params(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(uint8_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_6);
x_7 = 0;
return x_7;
}
case 1:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_StructInst_Struct_allDefault(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
return x_5;
}
}
default: 
{
return x_5;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
x_3 = 1;
x_4 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = 1;
x_8 = l_Lean_Name_toString(x_6, x_7);
x_9 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Nat_repr(x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l_Lean_Syntax_prettyPrint(x_13);
x_15 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4;
x_18 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_2);
x_20 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_4, x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
case 1:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Nat_repr(x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_2);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_20);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = l_Lean_Syntax_prettyPrint(x_32);
x_34 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2;
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
x_39 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_20);
return x_39;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" . ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" := ", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("<default>", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Elab_Term_StructInst_formatField___closed__2;
x_5 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_3, x_4);
x_6 = l_Lean_Elab_Term_StructInst_formatField___closed__4;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_Syntax_prettyPrint(x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_1(x_1, x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = l_Lean_Elab_Term_StructInst_formatField___closed__6;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_8 = l_Lean_Elab_Term_StructInst_formatField(x_7, x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_13 = l_Lean_Elab_Term_StructInst_formatField(x_12, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatStruct___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = 0;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_formatStxAux(x_6, x_7, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = 0;
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_formatStxAux(x_11, x_12, x_13, x_10);
lean_inc(x_2);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatStruct___spec__4(x_4, x_2);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[]", 2);
return x_1;
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_3 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4;
x_4 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatStruct___spec__4(x_1, x_3);
x_5 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2;
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6;
x_10 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = 0;
x_12 = lean_alloc_ctor(5, 1, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" .. }", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("#", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" with ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___closed__8;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(x_2, x_4);
x_6 = l_Lean_Elab_Term_StructInst_formatStruct___closed__1;
x_7 = l_Std_Format_joinSep___at_Prod_repr___spec__1(x_5, x_6);
lean_dec(x_5);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_Elab_Term_StructInst_formatStruct___closed__3;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_12 = l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
x_14 = l_Lean_Elab_Term_StructInst_formatStruct___closed__5;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2(x_18, x_19, x_16);
x_21 = lean_array_to_list(lean_box(0), x_20);
x_22 = l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3(x_21);
x_23 = l_Lean_Elab_Term_StructInst_formatStruct___closed__7;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Elab_Term_StructInst_formatStruct___closed__9;
x_28 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
x_30 = l_Lean_Elab_Term_StructInst_formatStruct___closed__3;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__2(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Std_Format_defWidth;
x_3 = lean_format_pretty(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_instToStringStruct___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1;
x_2 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatField), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringFieldStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("group", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
lean_inc(x_3);
x_6 = l_Lean_mkAtomFrom(x_3, x_5);
x_7 = l_Lean_mkIdentFrom(x_3, x_4);
x_8 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = lean_box(2);
x_12 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2;
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_mkIdentFrom(x_14, x_15);
return x_16;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
lean_inc(x_17);
x_19 = l_Lean_mkAtomFrom(x_17, x_18);
x_20 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_21 = lean_array_push(x_20, x_19);
x_22 = lean_array_push(x_21, x_17);
x_23 = lean_box(2);
x_24 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
return x_26;
}
}
default: 
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.StructInst.FieldVal.toSyntax", 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1;
x_3 = lean_unsigned_to_nat(322u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2;
x_4 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 0;
x_9 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_8, x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.StructInst.Field.toSyntax", 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1;
x_3 = lean_unsigned_to_nat(330u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2;
x_4 = l_panic___at_Lean_expandExplicitBindersAux_loop___spec__1(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(2u);
x_11 = l_Lean_Syntax_setArg(x_7, x_10, x_9);
x_12 = 1;
x_13 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_12, x_5);
x_14 = l_List_redLength___rarg(x_6);
x_15 = lean_mk_empty_array_with_capacity(x_14);
lean_dec(x_14);
x_16 = l_List_toArrayAux___rarg(x_6, x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_18, x_19, x_16);
x_21 = lean_box(2);
x_22 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_23 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_20);
x_24 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_25 = lean_array_push(x_24, x_13);
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_setArg(x_11, x_28, x_27);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected structure syntax", 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = l_Lean_Syntax_getKind(x_1);
x_5 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_6 = lean_name_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2;
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = l_Lean_Syntax_isIdent(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_Syntax_isFieldIdx_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1;
x_12 = l_Lean_Macro_throwError___rarg(x_11, x_2, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Syntax_getId(x_1);
x_17 = lean_erase_macro_scopes(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getArg(x_1, x_20);
lean_dec(x_1);
x_22 = l_Lean_Syntax_isIdent(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_Syntax_isFieldIdx_x3f(x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
x_24 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1;
x_25 = l_Lean_Macro_throwError___rarg(x_24, x_2, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Syntax_getId(x_21);
x_30 = lean_erase_macro_scopes(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_21);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
x_33 = lean_unsigned_to_nat(1u);
x_34 = l_Lean_Syntax_getArg(x_1, x_33);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_7, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_8, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_free_object(x_1);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
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
lean_free_object(x_1);
lean_dec(x_8);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_28 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_26, x_2, x_3);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_27, x_2, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_29);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_27);
x_41 = lean_ctor_get(x_28, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_43 = x_28;
} else {
 lean_dec_ref(x_28);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_7, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_7, x_11);
x_13 = l_Lean_Syntax_getArg(x_12, x_11);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_13, x_2, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_array_to_list(lean_box(0), x_19);
x_21 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_20, x_2, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_1, 0, x_15);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_10);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_8, x_2, x_23);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
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
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
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
lean_dec(x_15);
lean_dec(x_10);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
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
lean_dec(x_12);
lean_dec(x_10);
lean_free_object(x_1);
lean_dec(x_8);
lean_dec(x_7);
x_43 = !lean_is_exclusive(x_14);
if (x_43 == 0)
{
return x_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_1, 0);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_1);
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_getArg(x_47, x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_47, x_51);
x_53 = l_Lean_Syntax_getArg(x_52, x_51);
x_54 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_53, x_2, x_3);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_unsigned_to_nat(1u);
x_58 = l_Lean_Syntax_getArg(x_52, x_57);
lean_dec(x_52);
x_59 = l_Lean_Syntax_getArgs(x_58);
lean_dec(x_58);
x_60 = lean_array_to_list(lean_box(0), x_59);
x_61 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_60, x_2, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_50);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_47);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set(x_67, 3, x_66);
x_68 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_48, x_2, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_69);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_67);
x_74 = lean_ctor_get(x_68, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_55);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
x_78 = lean_ctor_get(x_61, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_61, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_80 = x_61;
} else {
 lean_dec_ref(x_61);
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
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
x_82 = lean_ctor_get(x_54, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_54, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_84 = x_54;
} else {
 lean_dec_ref(x_54);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_getSepArgs(x_7);
lean_dec(x_7);
x_9 = lean_array_to_list(lean_box(0), x_8);
x_10 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_9, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_12);
lean_ctor_set(x_14, 4, x_3);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_15);
lean_ctor_set(x_18, 4, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_5);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_apply_1(x_3, x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1), 6, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_6);
lean_closure_set(x_11, 4, x_8);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 3);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 3, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_11 = lean_apply_1(x_2, x_9);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_setFields___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_setParams(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_2);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_2);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_16; 
lean_dec(x_14);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_19;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_2);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
}
case 1:
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_15);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_4);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_4, 1);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_5);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_5, 1);
x_29 = lean_ctor_get(x_5, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_13, 0);
lean_inc(x_30);
lean_dec(x_13);
x_31 = l_Lean_Name_components(x_14);
x_32 = lean_box(0);
x_33 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_30, x_31, x_32);
x_34 = l_List_appendTR___rarg(x_33, x_28);
lean_ctor_set(x_4, 1, x_34);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_24;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_13, 0);
lean_inc(x_37);
lean_dec(x_13);
x_38 = l_Lean_Name_components(x_14);
x_39 = lean_box(0);
x_40 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_37, x_38, x_39);
x_41 = l_List_appendTR___rarg(x_40, x_36);
lean_ctor_set(x_4, 1, x_41);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_2);
x_1 = x_24;
x_2 = x_42;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 2);
x_46 = lean_ctor_get(x_4, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_48 = x_5;
} else {
 lean_dec_ref(x_5);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
lean_dec(x_13);
x_50 = l_Lean_Name_components(x_14);
x_51 = lean_box(0);
x_52 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_49, x_50, x_51);
x_53 = l_List_appendTR___rarg(x_52, x_47);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_45);
lean_ctor_set(x_54, 3, x_46);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_2);
x_1 = x_24;
x_2 = x_55;
goto _start;
}
}
default: 
{
lean_object* x_57; uint8_t x_58; 
lean_dec(x_15);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_4);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_4, 1);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_5);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_5, 1);
x_62 = lean_ctor_get(x_5, 0);
lean_dec(x_62);
x_63 = lean_ctor_get(x_13, 0);
lean_inc(x_63);
lean_dec(x_13);
x_64 = l_Lean_Name_components(x_14);
x_65 = lean_box(0);
x_66 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_63, x_64, x_65);
x_67 = l_List_appendTR___rarg(x_66, x_61);
lean_ctor_set(x_4, 1, x_67);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_57;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_5, 1);
lean_inc(x_69);
lean_dec(x_5);
x_70 = lean_ctor_get(x_13, 0);
lean_inc(x_70);
lean_dec(x_13);
x_71 = l_Lean_Name_components(x_14);
x_72 = lean_box(0);
x_73 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_70, x_71, x_72);
x_74 = l_List_appendTR___rarg(x_73, x_69);
lean_ctor_set(x_4, 1, x_74);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_4);
lean_ctor_set(x_75, 1, x_2);
x_1 = x_57;
x_2 = x_75;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = lean_ctor_get(x_4, 0);
x_78 = lean_ctor_get(x_4, 2);
x_79 = lean_ctor_get(x_4, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_4);
x_80 = lean_ctor_get(x_5, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_81 = x_5;
} else {
 lean_dec_ref(x_5);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_13, 0);
lean_inc(x_82);
lean_dec(x_13);
x_83 = l_Lean_Name_components(x_14);
x_84 = lean_box(0);
x_85 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_82, x_83, x_84);
x_86 = l_List_appendTR___rarg(x_85, x_80);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_78);
lean_ctor_set(x_87, 3, x_79);
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_2);
x_1 = x_57;
x_2 = x_88;
goto _start;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_14);
lean_dec(x_13);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_5, 1);
lean_dec(x_91);
x_92 = lean_ctor_get(x_5, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_1, 1);
lean_inc(x_93);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_93;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_5);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_4);
lean_ctor_set(x_96, 1, x_2);
x_1 = x_95;
x_2 = x_96;
goto _start;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_13);
x_98 = !lean_is_exclusive(x_5);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_5, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_5, 0);
lean_dec(x_100);
x_101 = lean_ctor_get(x_1, 1);
lean_inc(x_101);
lean_dec(x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_4);
x_1 = x_101;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_5);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
lean_dec(x_1);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_4);
lean_ctor_set(x_104, 1, x_2);
x_1 = x_103;
x_2 = x_104;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1;
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_8);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid field index, structure has only #", 41);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" fields", 7);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid field index, index must be greater than 0", 49);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_30; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_14 = x_2;
} else {
 lean_dec_ref(x_2);
 x_14 = lean_box(0);
}
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 1)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_12);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_12, 0);
x_34 = lean_ctor_get(x_12, 2);
x_35 = lean_ctor_get(x_12, 3);
x_36 = lean_ctor_get(x_12, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_30, 1);
x_39 = lean_ctor_get(x_30, 0);
lean_dec(x_39);
x_40 = !lean_is_exclusive(x_31);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_31, 0);
x_42 = lean_ctor_get(x_31, 1);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_eq(x_42, x_43);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_array_get_size(x_1);
x_46 = lean_nat_dec_lt(x_45, x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_42, x_47);
lean_dec(x_42);
x_49 = lean_nat_dec_lt(x_48, x_45);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_50 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_51 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_50);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 1, x_51);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_52; 
x_52 = lean_array_fget(x_1, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 1, x_52);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_free_object(x_31);
lean_dec(x_42);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_53 = l_Nat_repr(x_45);
x_54 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_41, x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
return x_60;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_31);
lean_dec(x_42);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_65 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
x_66 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_41, x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_31, 0);
x_72 = lean_ctor_get(x_31, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_31);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_array_get_size(x_1);
x_76 = lean_nat_dec_lt(x_75, x_72);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_72, x_77);
lean_dec(x_72);
x_79 = lean_nat_dec_lt(x_78, x_75);
lean_dec(x_75);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_78);
x_80 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_81 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_30, 0, x_82);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_array_fget(x_1, x_78);
lean_dec(x_78);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_30, 0, x_84);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_72);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_85 = l_Nat_repr(x_75);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_89 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
x_90 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_91 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_71, x_91, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_72);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_97 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
x_98 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_71, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_101 = x_98;
} else {
 lean_dec_ref(x_98);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_103 = lean_ctor_get(x_30, 1);
lean_inc(x_103);
lean_dec(x_30);
x_104 = lean_ctor_get(x_31, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_31, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_106 = x_31;
} else {
 lean_dec_ref(x_31);
 x_106 = lean_box(0);
}
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_array_get_size(x_1);
x_110 = lean_nat_dec_lt(x_109, x_105);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_105, x_111);
lean_dec(x_105);
x_113 = lean_nat_dec_lt(x_112, x_109);
lean_dec(x_109);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_112);
x_114 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_115 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_114);
if (lean_is_scalar(x_106)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_106;
 lean_ctor_set_tag(x_116, 0);
}
lean_ctor_set(x_116, 0, x_104);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_103);
lean_ctor_set(x_12, 1, x_117);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_array_fget(x_1, x_112);
lean_dec(x_112);
if (lean_is_scalar(x_106)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_106;
 lean_ctor_set_tag(x_119, 0);
}
lean_ctor_set(x_119, 0, x_104);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_103);
lean_ctor_set(x_12, 1, x_120);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_121 = l_Nat_repr(x_109);
x_122 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_125 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_104, x_127, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_103);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_133 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
x_134 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_104, x_133, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_139 = lean_ctor_get(x_12, 0);
x_140 = lean_ctor_get(x_12, 2);
x_141 = lean_ctor_get(x_12, 3);
lean_inc(x_141);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_12);
x_142 = lean_ctor_get(x_30, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_143 = x_30;
} else {
 lean_dec_ref(x_30);
 x_143 = lean_box(0);
}
x_144 = lean_ctor_get(x_31, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_31, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_146 = x_31;
} else {
 lean_dec_ref(x_31);
 x_146 = lean_box(0);
}
x_147 = lean_unsigned_to_nat(0u);
x_148 = lean_nat_dec_eq(x_145, x_147);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_array_get_size(x_1);
x_150 = lean_nat_dec_lt(x_149, x_145);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_sub(x_145, x_151);
lean_dec(x_145);
x_153 = lean_nat_dec_lt(x_152, x_149);
lean_dec(x_149);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_152);
x_154 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4;
x_155 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_154);
if (lean_is_scalar(x_146)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_146;
 lean_ctor_set_tag(x_156, 0);
}
lean_ctor_set(x_156, 0, x_144);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_143)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_143;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_142);
x_158 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_158, 0, x_139);
lean_ctor_set(x_158, 1, x_157);
lean_ctor_set(x_158, 2, x_140);
lean_ctor_set(x_158, 3, x_141);
x_15 = x_158;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_array_fget(x_1, x_152);
lean_dec(x_152);
if (lean_is_scalar(x_146)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_146;
 lean_ctor_set_tag(x_160, 0);
}
lean_ctor_set(x_160, 0, x_144);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_143)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_143;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_142);
x_162 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_162, 0, x_139);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set(x_162, 2, x_140);
lean_ctor_set(x_162, 3, x_141);
x_15 = x_162;
x_16 = x_9;
goto block_29;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
x_163 = l_Nat_repr(x_149);
x_164 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_167 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_169 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_144, x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_14);
lean_dec(x_13);
x_175 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
x_176 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_144, x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_30);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
}
block_29:
{
lean_object* x_17; 
x_17 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_14;
}
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_ctor_get(x_1, 4);
x_16 = lean_apply_8(x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_1, 3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_ctor_get(x_1, 4);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_1);
x_31 = lean_apply_8(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_30);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_dec(x_1);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.expandParentFields", 76);
return x_1;
}
}
static lean_object* _init_l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1;
x_3 = lean_unsigned_to_nat(429u);
x_4 = lean_unsigned_to_nat(28u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = l_Lean_Name_str___override(x_10, x_9);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_12);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = l_Lean_Name_str___override(x_16, x_15);
lean_inc(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
x_2 = x_14;
x_3 = x_19;
goto _start;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 0);
lean_dec(x_23);
x_24 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2;
x_25 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_24);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_25);
{
lean_object* _tmp_1 = x_22;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2;
x_29 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
x_2 = x_27;
x_3 = x_30;
goto _start;
}
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a field of structure '", 31);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to access field '", 24);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' in parent structure", 21);
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_15 = x_3;
} else {
 lean_dec_ref(x_3);
 x_15 = lean_box(0);
}
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_13, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_38);
lean_inc(x_2);
x_39 = l_Lean_findField_x3f(x_2, x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_2);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_41 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_36, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_name_eq(x_53, x_38);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_13);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_13, 3);
lean_dec(x_56);
x_57 = lean_ctor_get(x_13, 2);
lean_dec(x_57);
x_58 = lean_ctor_get(x_13, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_13, 0);
lean_dec(x_59);
lean_inc(x_2);
x_60 = l_Lean_getPathToBaseStructure_x3f(x_2, x_53, x_38);
lean_dec(x_53);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_13);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_61 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_61, 0, x_37);
x_62 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_36, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
return x_66;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_37);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = lean_box(0);
x_73 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(x_36, x_71, x_72);
x_74 = l_List_appendTR___rarg(x_73, x_31);
lean_ctor_set(x_13, 1, x_74);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
else
{
lean_object* x_75; 
lean_dec(x_13);
lean_inc(x_2);
x_75 = l_Lean_getPathToBaseStructure_x3f(x_2, x_53, x_38);
lean_dec(x_53);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_37);
x_77 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6;
x_78 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8;
x_80 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_36, x_80, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
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
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_37);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
lean_dec(x_75);
x_87 = lean_box(0);
x_88 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(x_36, x_86, x_87);
x_89 = l_List_appendTR___rarg(x_88, x_31);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_33);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_90, 2, x_34);
lean_ctor_set(x_90, 3, x_35);
x_16 = x_90;
x_17 = x_10;
goto block_30;
}
}
}
else
{
lean_dec(x_53);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_31);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
block_30:
{
lean_object* x_18; 
x_18 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_is_scalar(x_15)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_15;
}
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
if (lean_is_scalar(x_15)) {
 x_24 = lean_alloc_ctor(1, 2, 0);
} else {
 x_24 = x_15;
}
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_dec(x_15);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___boxed), 10, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1;
x_10 = lean_panic_fn(x_9, x_1);
x_11 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_8);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_to_usize(x_5);
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
lean_dec(x_3);
x_9 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash___override(x_13);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = lean_uint64_to_usize(x_8);
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_14);
x_18 = lean_nat_dec_le(x_17, x_7);
lean_dec(x_7);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_14, x_16);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(x_2, x_3, x_11);
x_21 = lean_array_uset(x_6, x_10, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = l_Lean_Name_hash___override(x_2);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_modn(x_26, x_24);
x_28 = lean_array_uget(x_23, x_27);
x_29 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(x_2, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_22, x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_28);
x_33 = lean_array_uset(x_23, x_27, x_32);
x_34 = l___private_Std_Data_HashMap_0__Std_numBucketsForCapacity(x_31);
x_35 = lean_nat_dec_le(x_34, x_24);
lean_dec(x_24);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_31, x_33);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(x_2, x_3, x_28);
x_39 = lean_array_uset(x_23, x_27, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.mkFieldMap", 68);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1;
x_3 = lean_unsigned_to_nat(447u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("field '", 7);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' has already beed specified", 28);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_1 = x_16;
x_2 = x_13;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
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
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_dec(x_25);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_41; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_27);
lean_inc(x_1);
x_41 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(x_1, x_27);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_11);
x_43 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_27, x_12);
x_1 = x_43;
x_2 = x_26;
goto _start;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_box(0);
lean_ctor_set(x_12, 1, x_46);
lean_ctor_set(x_12, 0, x_11);
x_47 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_27, x_12);
x_1 = x_47;
x_2 = x_26;
goto _start;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_45, 0);
x_51 = lean_ctor_get(x_45, 1);
x_52 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_50);
if (x_53 == 0)
{
lean_object* x_54; 
lean_ctor_set(x_12, 1, x_45);
lean_ctor_set(x_12, 0, x_11);
x_54 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_27, x_12);
x_1 = x_54;
x_2 = x_26;
goto _start;
}
else
{
lean_object* x_56; 
lean_free_object(x_45);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_26);
lean_free_object(x_12);
lean_dec(x_1);
x_56 = lean_box(0);
x_28 = x_56;
goto block_40;
}
}
else
{
lean_object* x_57; 
lean_free_object(x_45);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_26);
lean_free_object(x_12);
lean_dec(x_1);
x_57 = lean_box(0);
x_28 = x_57;
goto block_40;
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_45, 0);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_45);
x_60 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_60 == 0)
{
uint8_t x_61; 
x_61 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_12, 1, x_62);
lean_ctor_set(x_12, 0, x_11);
x_63 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_27, x_12);
x_1 = x_63;
x_2 = x_26;
goto _start;
}
else
{
lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_26);
lean_free_object(x_12);
lean_dec(x_1);
x_65 = lean_box(0);
x_28 = x_65;
goto block_40;
}
}
else
{
lean_object* x_66; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_26);
lean_free_object(x_12);
lean_dec(x_1);
x_66 = lean_box(0);
x_28 = x_66;
goto block_40;
}
}
}
}
block_40:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_28);
x_29 = lean_ctor_get(x_11, 0);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_30, 0, x_27);
x_31 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(x_29, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_free_object(x_12);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_1);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
lean_dec(x_2);
x_68 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_69 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_1 = x_70;
x_2 = x_67;
x_9 = x_71;
goto _start;
}
else
{
uint8_t x_73; 
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_12, 0);
lean_inc(x_77);
lean_dec(x_12);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_93; 
x_78 = lean_ctor_get(x_2, 1);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_79);
lean_inc(x_1);
x_93 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(x_1, x_79);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_11);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_79, x_95);
x_1 = x_96;
x_2 = x_78;
goto _start;
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
lean_dec(x_93);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_11);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_79, x_100);
x_1 = x_101;
x_2 = x_78;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_105 = x_98;
} else {
 lean_dec_ref(x_98);
 x_105 = lean_box(0);
}
x_106 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_103);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
if (lean_is_scalar(x_105)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_105;
}
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_11);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Std_HashMap_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_1, x_79, x_109);
x_1 = x_110;
x_2 = x_78;
goto _start;
}
else
{
lean_object* x_112; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_78);
lean_dec(x_1);
x_112 = lean_box(0);
x_80 = x_112;
goto block_92;
}
}
else
{
lean_object* x_113; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_78);
lean_dec(x_1);
x_113 = lean_box(0);
x_80 = x_113;
goto block_92;
}
}
}
block_92:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_80);
x_81 = lean_ctor_get(x_11, 0);
lean_inc(x_81);
lean_dec(x_11);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_79);
x_83 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(x_81, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
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
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_77);
lean_dec(x_11);
lean_dec(x_1);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_dec(x_2);
x_115 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_116 = l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_1 = x_117;
x_2 = x_114;
x_9 = x_118;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_120 = lean_ctor_get(x_116, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_122 = x_116;
} else {
 lean_dec_ref(x_116);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Std_mkHashMapImp___rarg(x_9);
x_11 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(lean_object* x_1) {
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
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is not a valid field of '", 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdx_x3f_loop___rarg(x_2, x_11, x_12, x_13, lean_box(0));
lean_dec(x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_20, 0, x_1);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3;
lean_inc(x_1);
x_12 = l_Lean_mkAtomFrom(x_1, x_11);
lean_inc(x_1);
x_13 = l_Lean_mkIdentFrom(x_1, x_2);
x_14 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20;
x_15 = lean_array_push(x_14, x_1);
x_16 = lean_array_push(x_15, x_12);
x_17 = lean_array_push(x_16, x_13);
x_18 = lean_box(2);
x_19 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13;
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_findField_x3f(x_15, x_2, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_free_object(x_11);
x_18 = lean_box(0);
x_19 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1(x_1, x_3, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_findField_x3f(x_22, x_2, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1(x_1, x_3, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_mkProjStx_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_name_eq(x_7, x_1);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_find_x3f___rarg(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_List_tail_x21___rarg(x_8);
lean_ctor_set(x_5, 1, x_9);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_7;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_5, 2);
x_15 = lean_ctor_get(x_5, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_16 = l_List_tail_x21___rarg(x_13);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_15);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_11;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 3);
lean_inc(x_24);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 lean_ctor_release(x_19, 3);
 x_25 = x_19;
} else {
 lean_dec_ref(x_19);
 x_25 = lean_box(0);
}
x_26 = l_List_tail_x21___rarg(x_22);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 4, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
x_1 = x_20;
x_2 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f(x_15, x_16, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_12 = x_19;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_array_push(x_5, x_24);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_5 = x_25;
x_12 = x_23;
goto _start;
}
}
else
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_5);
lean_ctor_set(x_29, 1, x_12);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_2);
x_16 = lean_nat_dec_le(x_4, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_20 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_21 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_22 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4(x_1, x_2, x_19, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instInhabitedField(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_16 = x_4;
} else {
 lean_dec_ref(x_4);
 x_16 = lean_box(0);
}
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_dec(x_14);
x_34 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_57; lean_object* x_58; 
x_35 = lean_box(0);
lean_inc(x_33);
x_36 = l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__1(x_33, x_35);
x_37 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1;
x_38 = l_List_head_x21___rarg(x_37, x_33);
lean_dec(x_33);
x_57 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_32);
lean_inc(x_2);
x_58 = l_Lean_isSubobjectField_x3f(x_2, x_57, x_32);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_59 = lean_unsigned_to_nat(4u);
x_60 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4;
lean_inc(x_3);
x_61 = l_Lean_Syntax_setArg(x_3, x_59, x_60);
x_62 = l_List_redLength___rarg(x_36);
x_63 = lean_mk_empty_array_with_capacity(x_62);
lean_dec(x_62);
x_64 = l_List_toArrayAux___rarg(x_36, x_63);
x_65 = lean_array_get_size(x_64);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2(x_66, x_67, x_64);
x_69 = l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5;
x_70 = l_Lean_mkSepArray(x_68, x_69);
lean_dec(x_68);
x_71 = lean_box(2);
x_72 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3;
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_unsigned_to_nat(2u);
x_75 = l_Lean_Syntax_setArg(x_61, x_74, x_73);
x_76 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_76)) {
case 0:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_32);
x_77 = lean_unsigned_to_nat(1u);
x_78 = l_Lean_Syntax_setArg(x_75, x_77, x_60);
x_79 = lean_unsigned_to_nat(3u);
x_80 = l_Lean_Syntax_setArg(x_78, x_79, x_60);
x_39 = x_80;
x_40 = x_11;
goto block_56;
}
case 1:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_32);
x_81 = lean_ctor_get(x_76, 0);
lean_inc(x_81);
lean_dec(x_76);
x_82 = lean_unsigned_to_nat(1u);
x_83 = l_Lean_Syntax_setArg(x_75, x_82, x_60);
x_84 = lean_unsigned_to_nat(3u);
x_85 = l_Lean_Syntax_setArg(x_83, x_84, x_81);
x_39 = x_85;
x_40 = x_11;
goto block_56;
}
default: 
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_array_get_size(x_86);
x_88 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_89 = l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3(x_32, x_86, x_88, x_87, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_86);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Array_isEmpty___rarg(x_90);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax(x_90);
lean_dec(x_90);
x_94 = lean_unsigned_to_nat(1u);
x_95 = l_Lean_Syntax_setArg(x_75, x_94, x_93);
x_96 = lean_unsigned_to_nat(3u);
x_97 = l_Lean_Syntax_setArg(x_95, x_96, x_60);
x_39 = x_97;
x_40 = x_91;
goto block_56;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_90);
x_98 = lean_unsigned_to_nat(1u);
x_99 = l_Lean_Syntax_setArg(x_75, x_98, x_60);
x_100 = lean_unsigned_to_nat(3u);
x_101 = l_Lean_Syntax_setArg(x_99, x_100, x_60);
x_39 = x_101;
x_40 = x_91;
goto block_56;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_32);
x_102 = lean_ctor_get(x_58, 0);
lean_inc(x_102);
lean_dec(x_58);
x_103 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
x_104 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_inc(x_3);
x_105 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_105, 0, x_3);
lean_ctor_set(x_105, 1, x_102);
lean_ctor_set(x_105, 2, x_104);
lean_ctor_set(x_105, 3, x_36);
lean_ctor_set(x_105, 4, x_103);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_106 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_105, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = !lean_is_exclusive(x_38);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_38, 1);
x_111 = lean_ctor_get(x_38, 2);
lean_dec(x_111);
x_112 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_113 = l_List_head_x21___rarg(x_112, x_110);
lean_dec(x_110);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_35);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_38, 2, x_115);
lean_ctor_set(x_38, 1, x_114);
x_17 = x_38;
x_18 = x_108;
goto block_31;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_38, 0);
x_117 = lean_ctor_get(x_38, 1);
x_118 = lean_ctor_get(x_38, 3);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_38);
x_119 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_120 = l_List_head_x21___rarg(x_119, x_117);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_35);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_107);
x_123 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_121);
lean_ctor_set(x_123, 2, x_122);
lean_ctor_set(x_123, 3, x_118);
x_17 = x_123;
x_18 = x_108;
goto block_31;
}
}
else
{
uint8_t x_124; 
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_106);
if (x_124 == 0)
{
return x_106;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_106, 0);
x_126 = lean_ctor_get(x_106, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_106);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
block_56:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_38, 1);
x_43 = lean_ctor_get(x_38, 2);
lean_dec(x_43);
x_44 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_45 = l_List_head_x21___rarg(x_44, x_42);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_35);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_46);
x_17 = x_38;
x_18 = x_40;
goto block_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_38, 0);
x_49 = lean_ctor_get(x_38, 1);
x_50 = lean_ctor_get(x_38, 3);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_38);
x_51 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_52 = l_List_head_x21___rarg(x_51, x_49);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_35);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_39);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_53);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_50);
x_17 = x_55;
x_18 = x_40;
goto block_31;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_33);
lean_dec(x_32);
x_128 = lean_ctor_get(x_34, 0);
lean_inc(x_128);
lean_dec(x_34);
x_17 = x_128;
x_18 = x_11;
goto block_31;
}
block_31:
{
lean_object* x_19; 
x_19 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
if (lean_is_scalar(x_16)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_16;
}
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
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
if (lean_is_scalar(x_16)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_16;
}
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_16);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__5(x_13);
x_16 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_inc(x_13);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1___boxed), 11, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_13);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 5);
x_17 = l_Lean_replaceRef(x_13, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_ctor_set(x_6, 5, x_17);
x_18 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = lean_ctor_get(x_6, 2);
x_22 = lean_ctor_get(x_6, 3);
x_23 = lean_ctor_get(x_6, 4);
x_24 = lean_ctor_get(x_6, 5);
x_25 = lean_ctor_get(x_6, 6);
x_26 = lean_ctor_get(x_6, 7);
x_27 = lean_ctor_get(x_6, 8);
x_28 = lean_ctor_get(x_6, 9);
x_29 = lean_ctor_get(x_6, 10);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_30 = l_Lean_replaceRef(x_13, x_24);
lean_dec(x_24);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_21);
lean_ctor_set(x_31, 3, x_22);
lean_ctor_set(x_31, 4, x_23);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_25);
lean_ctor_set(x_31, 7, x_26);
lean_ctor_set(x_31, 8, x_27);
lean_ctor_set(x_31, 9, x_28);
lean_ctor_set(x_31, 10, x_29);
x_32 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_14, x_2, x_3, x_4, x_5, x_31, x_7, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1;
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f(x_17, x_18, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
lean_inc(x_2);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_12 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_20);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = l_Lean_Elab_Term_StructInst_mkProjStx_x3f(x_17, x_18, x_1, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
lean_inc(x_2);
{
size_t _tmp_4 = x_23;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_12 = x_21;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_20);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_19, 0, x_35);
return x_19;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_38 = x_20;
} else {
 lean_dec_ref(x_20);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 1, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
}
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1() {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_eq(x_6, x_7);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_42; lean_object* x_43; 
x_17 = lean_array_uget(x_5, x_6);
x_42 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_17);
x_43 = l_Lean_Elab_Term_StructInst_findField_x3f(x_42, x_17);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_inc(x_17);
lean_inc(x_3);
lean_inc(x_2);
x_44 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_17);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_45)) {
case 0:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_box(2);
lean_inc(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_4);
lean_ctor_set(x_47, 1, x_17);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_box(0);
lean_inc(x_4);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_46);
lean_ctor_set(x_51, 3, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_8);
x_18 = x_52;
x_19 = x_15;
goto block_23;
}
case 1:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_45);
lean_inc(x_4);
x_53 = l_Lean_mkHole(x_4);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_inc(x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_17);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_box(0);
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_57);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_58);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_8);
x_18 = x_60;
x_19 = x_15;
goto block_23;
}
default: 
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_45, 0);
lean_inc(x_61);
lean_dec(x_45);
x_62 = lean_box(0);
x_63 = lean_array_get_size(x_61);
x_64 = lean_usize_of_nat(x_63);
lean_dec(x_63);
x_65 = 0;
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1;
lean_inc(x_17);
x_67 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1(x_17, x_66, x_61, x_64, x_65, x_66, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_61);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_24 = x_62;
x_25 = x_70;
goto block_41;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_ctor_get(x_69, 0);
lean_inc(x_72);
lean_dec(x_69);
x_24 = x_72;
x_25 = x_71;
goto block_41;
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_44, 0);
lean_inc(x_73);
lean_dec(x_44);
x_74 = lean_box(0);
x_75 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
x_76 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_inc(x_75);
lean_inc(x_4);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_4);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
if (lean_obj_tag(x_75) == 2)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_75, 0);
lean_inc(x_101);
lean_dec(x_75);
x_102 = lean_box(0);
x_103 = lean_array_get_size(x_101);
x_104 = lean_usize_of_nat(x_103);
lean_dec(x_103);
x_105 = 0;
x_106 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1;
lean_inc(x_17);
x_107 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2(x_17, x_106, x_101, x_104, x_105, x_106, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_101);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_78 = x_102;
x_79 = x_110;
goto block_100;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_dec(x_107);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
lean_dec(x_109);
x_78 = x_112;
x_79 = x_111;
goto block_100;
}
}
else
{
lean_object* x_113; 
lean_dec(x_75);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_113 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_77, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_114);
lean_inc(x_4);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_4);
lean_ctor_set(x_117, 1, x_17);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_74);
x_119 = lean_box(0);
lean_inc(x_4);
x_120 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_120, 0, x_4);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_116);
lean_ctor_set(x_120, 3, x_119);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_8);
x_18 = x_121;
x_19 = x_115;
goto block_23;
}
else
{
uint8_t x_122; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_113);
if (x_122 == 0)
{
return x_113;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_113, 0);
x_124 = lean_ctor_get(x_113, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_113);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
block_100:
{
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_80; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_80 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_77, x_9, x_10, x_11, x_12, x_13, x_14, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_81);
lean_inc(x_4);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_4);
lean_ctor_set(x_84, 1, x_17);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_74);
x_86 = lean_box(0);
lean_inc(x_4);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_4);
lean_ctor_set(x_87, 1, x_85);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_86);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_8);
x_18 = x_88;
x_19 = x_82;
goto block_23;
}
else
{
uint8_t x_89; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_80);
if (x_89 == 0)
{
return x_80;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_80, 0);
x_91 = lean_ctor_get(x_80, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_80);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_77);
x_93 = lean_ctor_get(x_78, 0);
lean_inc(x_93);
lean_dec(x_78);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
lean_inc(x_4);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_4);
lean_ctor_set(x_95, 1, x_17);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_74);
x_97 = lean_box(0);
lean_inc(x_4);
x_98 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_98, 0, x_4);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 2, x_94);
lean_ctor_set(x_98, 3, x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_8);
x_18 = x_99;
x_19 = x_79;
goto block_23;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_17);
x_126 = lean_ctor_get(x_43, 0);
lean_inc(x_126);
lean_dec(x_43);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_8);
x_18 = x_127;
x_19 = x_15;
goto block_23;
}
block_23:
{
size_t x_20; size_t x_21; 
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
x_8 = x_18;
x_15 = x_19;
goto _start;
}
block_41:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_box(2);
lean_inc(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_17);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_8);
x_18 = x_32;
x_19 = x_25;
goto block_23;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_17);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_4);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
x_18 = x_40;
x_19 = x_25;
goto block_23;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_8);
lean_ctor_set(x_128, 1, x_15);
return x_128;
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_List_reverse___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_17 = l_Lean_Syntax_mkSynthetic(x_16);
x_18 = lean_box(0);
x_19 = lean_array_get_size(x_15);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_23 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_22);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_6, 5);
x_26 = l_Lean_replaceRef(x_17, x_25);
lean_dec(x_25);
lean_ctor_set(x_6, 5, x_26);
x_27 = lean_nat_dec_le(x_19, x_19);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_29 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_28);
lean_ctor_set(x_9, 0, x_29);
return x_9;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
lean_free_object(x_9);
x_30 = 0;
x_31 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(x_1, x_13, x_14, x_17, x_15, x_30, x_31, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_List_reverse___rarg(x_34);
x_36 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = l_List_reverse___rarg(x_37);
x_40 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_46 = lean_ctor_get(x_6, 0);
x_47 = lean_ctor_get(x_6, 1);
x_48 = lean_ctor_get(x_6, 2);
x_49 = lean_ctor_get(x_6, 3);
x_50 = lean_ctor_get(x_6, 4);
x_51 = lean_ctor_get(x_6, 5);
x_52 = lean_ctor_get(x_6, 6);
x_53 = lean_ctor_get(x_6, 7);
x_54 = lean_ctor_get(x_6, 8);
x_55 = lean_ctor_get(x_6, 9);
x_56 = lean_ctor_get(x_6, 10);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_6);
x_57 = l_Lean_replaceRef(x_17, x_51);
lean_dec(x_51);
x_58 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_58, 0, x_46);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_48);
lean_ctor_set(x_58, 3, x_49);
lean_ctor_set(x_58, 4, x_50);
lean_ctor_set(x_58, 5, x_57);
lean_ctor_set(x_58, 6, x_52);
lean_ctor_set(x_58, 7, x_53);
lean_ctor_set(x_58, 8, x_54);
lean_ctor_set(x_58, 9, x_55);
lean_ctor_set(x_58, 10, x_56);
x_59 = lean_nat_dec_le(x_19, x_19);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_58);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_61 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_60);
lean_ctor_set(x_9, 0, x_61);
return x_9;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; 
lean_free_object(x_9);
x_62 = 0;
x_63 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_64 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(x_1, x_13, x_14, x_17, x_15, x_62, x_63, x_18, x_2, x_3, x_4, x_5, x_58, x_7, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = l_List_reverse___rarg(x_65);
x_69 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_68);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_73 = x_64;
} else {
 lean_dec_ref(x_64);
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
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_75 = lean_ctor_get(x_9, 0);
x_76 = lean_ctor_get(x_9, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_9);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_78);
lean_inc(x_77);
x_79 = l_Lean_getStructureFields(x_77, x_78);
x_80 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_81 = l_Lean_Syntax_mkSynthetic(x_80);
x_82 = lean_box(0);
x_83 = lean_array_get_size(x_79);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_87 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_89 = lean_ctor_get(x_6, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_6, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_6, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_6, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_6, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_6, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_6, 6);
lean_inc(x_95);
x_96 = lean_ctor_get(x_6, 7);
lean_inc(x_96);
x_97 = lean_ctor_get(x_6, 8);
lean_inc(x_97);
x_98 = lean_ctor_get(x_6, 9);
lean_inc(x_98);
x_99 = lean_ctor_get(x_6, 10);
lean_inc(x_99);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 x_100 = x_6;
} else {
 lean_dec_ref(x_6);
 x_100 = lean_box(0);
}
x_101 = l_Lean_replaceRef(x_81, x_94);
lean_dec(x_94);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 11, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_89);
lean_ctor_set(x_102, 1, x_90);
lean_ctor_set(x_102, 2, x_91);
lean_ctor_set(x_102, 3, x_92);
lean_ctor_set(x_102, 4, x_93);
lean_ctor_set(x_102, 5, x_101);
lean_ctor_set(x_102, 6, x_95);
lean_ctor_set(x_102, 7, x_96);
lean_ctor_set(x_102, 8, x_97);
lean_ctor_set(x_102, 9, x_98);
lean_ctor_set(x_102, 10, x_99);
x_103 = lean_nat_dec_le(x_83, x_83);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_102);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_104 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_105 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_76);
return x_106;
}
else
{
size_t x_107; size_t x_108; lean_object* x_109; 
x_107 = 0;
x_108 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_109 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(x_1, x_77, x_78, x_81, x_79, x_107, x_108, x_82, x_2, x_3, x_4, x_5, x_102, x_7, x_76);
lean_dec(x_79);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_112 = x_109;
} else {
 lean_dec_ref(x_109);
 x_112 = lean_box(0);
}
x_113 = l_List_reverse___rarg(x_110);
x_114 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_113);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_116 = lean_ctor_get(x_109, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_109, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_118 = x_109;
} else {
 lean_dec_ref(x_109);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_filterMapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__6(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__7(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__2(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected constructor type", 27);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_1, x_15);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Meta_whnfForall(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 7)
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3 + 8);
x_20 = lean_box(x_19);
if (lean_obj_tag(x_20) == 3)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 2);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = 1;
x_27 = lean_box(0);
lean_inc(x_8);
x_28 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_25, x_26, x_27, x_8, x_9, x_10, x_11, x_21);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_expr_instantiate1(x_24, x_29);
lean_dec(x_24);
lean_inc(x_29);
x_32 = l_Lean_Expr_app___override(x_3, x_29);
lean_inc(x_29);
x_33 = l_Lean_Expr_mvarId_x21(x_29);
x_34 = lean_array_push(x_4, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_22);
lean_ctor_set(x_35, 1, x_29);
x_36 = lean_array_push(x_5, x_35);
x_1 = x_16;
x_2 = x_31;
x_3 = x_32;
x_4 = x_34;
x_5 = x_36;
x_12 = x_30;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_20);
x_38 = lean_ctor_get(x_17, 1);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_ctor_get(x_18, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 2);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_40);
x_43 = 0;
x_44 = lean_box(0);
lean_inc(x_8);
x_45 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_42, x_43, x_44, x_8, x_9, x_10, x_11, x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_expr_instantiate1(x_41, x_46);
lean_dec(x_41);
lean_inc(x_46);
x_49 = l_Lean_Expr_app___override(x_3, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_array_push(x_5, x_50);
x_1 = x_16;
x_2 = x_48;
x_3 = x_49;
x_5 = x_51;
x_12 = x_47;
goto _start;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_dec(x_17);
x_54 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2;
x_55 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_53);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_17);
if (x_56 == 0)
{
return x_17;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_3);
lean_ctor_set(x_60, 1, x_2);
lean_ctor_set(x_60, 2, x_4);
lean_ctor_set(x_60, 3, x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_12);
return x_61;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody(x_2, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Expr_hasLooseBVars(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Lean_Meta_isExprDefEq(x_13, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_10);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_List_lengthTRAux___rarg(x_11, x_12);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_mkFreshLevelMVars(x_13, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
lean_inc(x_15);
x_18 = l_Lean_Expr_const___override(x_17, x_15);
lean_inc(x_1);
x_19 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_inc(x_8);
lean_inc(x_7);
x_20 = l_Lean_Core_instantiateTypeLevelParams(x_19, x_15, x_7, x_8, x_16);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(x_23, x_21, x_18, x_24, x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(x_28, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_26, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
x_34 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_32, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_26);
return x_34;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_26);
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
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
lean_dec(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_25);
if (x_47 == 0)
{
return x_25;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_25, 0);
x_49 = lean_ctor_get(x_25, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_25);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("structInstDefault", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to elaborate field '", 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' of '", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
x_15 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_6);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_allDefault(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_Meta_synthInstance_x3f(x_2, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_14, 0);
lean_dec(x_20);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_8);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2;
x_3 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1;
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
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("byTactic", 8);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10;
x_2 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("by", 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_expr_consume_type_annotations(x_20);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(0);
x_26 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_27 = l_Lean_Elab_Term_elabTermEnsuringType(x_22, x_24, x_26, x_26, x_25, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_3);
x_31 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_28);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_5);
x_33 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_35, x_12, x_13, x_14, x_15, x_16, x_17, x_29);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_inc(x_28);
x_39 = l_Lean_Expr_app___override(x_6, x_28);
x_40 = lean_expr_instantiate1(x_21, x_28);
lean_dec(x_21);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_28);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_7);
lean_ctor_set(x_43, 2, x_19);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_8);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_9);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_36, 0, x_47);
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
lean_inc(x_28);
x_49 = l_Lean_Expr_app___override(x_6, x_28);
x_50 = lean_expr_instantiate1(x_21, x_28);
lean_dec(x_21);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_28);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_7);
lean_ctor_set(x_53, 2, x_19);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_9);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_48);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_27);
if (x_59 == 0)
{
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_10);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_19);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_63);
lean_inc(x_66);
x_67 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_66, x_63, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_63);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_70);
x_71 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_66, x_70, x_12, x_13, x_14, x_15, x_16, x_17, x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_72, 2);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_78 = l_Lean_Elab_Term_ensureHasType(x_70, x_74, x_77, x_12, x_13, x_14, x_15, x_16, x_17, x_73);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_2, 0);
lean_inc(x_81);
lean_dec(x_2);
lean_ctor_set(x_19, 0, x_75);
x_82 = l_Array_append___rarg(x_9, x_76);
x_83 = lean_ctor_get(x_14, 1);
lean_inc(x_83);
lean_inc(x_3);
x_84 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_79);
x_85 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_3);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_85, 4, x_5);
x_86 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_88, x_12, x_13, x_14, x_15, x_16, x_17, x_80);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
lean_inc(x_79);
x_92 = l_Lean_Expr_app___override(x_6, x_79);
x_93 = lean_expr_instantiate1(x_64, x_79);
lean_dec(x_64);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_79);
x_95 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_95, 0, x_81);
lean_ctor_set(x_95, 1, x_7);
lean_ctor_set(x_95, 2, x_19);
lean_ctor_set(x_95, 3, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_8);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_82);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_92);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_89, 0, x_99);
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
lean_dec(x_89);
lean_inc(x_79);
x_101 = l_Lean_Expr_app___override(x_6, x_79);
x_102 = lean_expr_instantiate1(x_64, x_79);
lean_dec(x_64);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_79);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_81);
lean_ctor_set(x_104, 1, x_7);
lean_ctor_set(x_104, 2, x_19);
lean_ctor_set(x_104, 3, x_103);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_8);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_82);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_102);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_101);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_100);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_19);
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_78);
if (x_110 == 0)
{
return x_78;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_78, 0);
x_112 = lean_ctor_get(x_78, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_78);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_70);
lean_free_object(x_19);
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_71);
if (x_114 == 0)
{
return x_71;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_71, 0);
x_116 = lean_ctor_get(x_71, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_71);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; uint8_t x_119; 
lean_dec(x_66);
lean_dec(x_63);
x_118 = lean_ctor_get(x_67, 1);
lean_inc(x_118);
lean_dec(x_67);
x_119 = !lean_is_exclusive(x_68);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_120 = lean_ctor_get(x_68, 0);
x_121 = lean_ctor_get(x_2, 0);
lean_inc(x_121);
lean_dec(x_2);
lean_inc(x_121);
x_122 = l_Lean_mkHole(x_121);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_122);
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
lean_inc(x_3);
x_124 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_120);
x_125 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_3);
lean_ctor_set(x_125, 2, x_123);
lean_ctor_set(x_125, 3, x_120);
lean_ctor_set(x_125, 4, x_5);
x_126 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_128, x_12, x_13, x_14, x_15, x_16, x_17, x_118);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_131 = lean_ctor_get(x_129, 0);
lean_dec(x_131);
lean_inc(x_120);
x_132 = l_Lean_Expr_app___override(x_6, x_120);
x_133 = lean_expr_instantiate1(x_64, x_120);
lean_dec(x_64);
x_134 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_7);
lean_ctor_set(x_134, 2, x_19);
lean_ctor_set(x_134, 3, x_68);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_8);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_9);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_132);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_129, 0, x_138);
return x_129;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_129, 1);
lean_inc(x_139);
lean_dec(x_129);
lean_inc(x_120);
x_140 = l_Lean_Expr_app___override(x_6, x_120);
x_141 = lean_expr_instantiate1(x_64, x_120);
lean_dec(x_64);
x_142 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_142, 0, x_121);
lean_ctor_set(x_142, 1, x_7);
lean_ctor_set(x_142, 2, x_19);
lean_ctor_set(x_142, 3, x_68);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_8);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_9);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_139);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_148 = lean_ctor_get(x_68, 0);
lean_inc(x_148);
lean_dec(x_68);
x_149 = lean_ctor_get(x_2, 0);
lean_inc(x_149);
lean_dec(x_2);
lean_inc(x_149);
x_150 = l_Lean_mkHole(x_149);
lean_ctor_set_tag(x_19, 0);
lean_ctor_set(x_19, 0, x_150);
x_151 = lean_ctor_get(x_14, 1);
lean_inc(x_151);
lean_inc(x_3);
x_152 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_148);
x_153 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_3);
lean_ctor_set(x_153, 2, x_151);
lean_ctor_set(x_153, 3, x_148);
lean_ctor_set(x_153, 4, x_5);
x_154 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_156, x_12, x_13, x_14, x_15, x_16, x_17, x_118);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
lean_inc(x_148);
x_160 = l_Lean_Expr_app___override(x_6, x_148);
x_161 = lean_expr_instantiate1(x_64, x_148);
lean_dec(x_64);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_148);
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_149);
lean_ctor_set(x_163, 1, x_7);
lean_ctor_set(x_163, 2, x_19);
lean_ctor_set(x_163, 3, x_162);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_8);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_9);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_166);
if (lean_is_scalar(x_159)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_159;
}
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_158);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_19, 0);
lean_inc(x_169);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_63);
lean_inc(x_169);
x_170 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_169, x_63, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_63);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_173);
x_174 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_169, x_173, x_12, x_13, x_14, x_15, x_16, x_17, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
x_179 = lean_ctor_get(x_175, 2);
lean_inc(x_179);
lean_dec(x_175);
x_180 = lean_box(0);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_181 = l_Lean_Elab_Term_ensureHasType(x_173, x_177, x_180, x_12, x_13, x_14, x_15, x_16, x_17, x_176);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_2, 0);
lean_inc(x_184);
lean_dec(x_2);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_178);
x_186 = l_Array_append___rarg(x_9, x_179);
x_187 = lean_ctor_get(x_14, 1);
lean_inc(x_187);
lean_inc(x_3);
x_188 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_182);
x_189 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_3);
lean_ctor_set(x_189, 2, x_187);
lean_ctor_set(x_189, 3, x_182);
lean_ctor_set(x_189, 4, x_5);
x_190 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_192, x_12, x_13, x_14, x_15, x_16, x_17, x_183);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_195 = x_193;
} else {
 lean_dec_ref(x_193);
 x_195 = lean_box(0);
}
lean_inc(x_182);
x_196 = l_Lean_Expr_app___override(x_6, x_182);
x_197 = lean_expr_instantiate1(x_64, x_182);
lean_dec(x_64);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_182);
x_199 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_199, 0, x_184);
lean_ctor_set(x_199, 1, x_7);
lean_ctor_set(x_199, 2, x_185);
lean_ctor_set(x_199, 3, x_198);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_8);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_186);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_196);
lean_ctor_set(x_203, 1, x_202);
if (lean_is_scalar(x_195)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_195;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_194);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_181, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_181, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_207 = x_181;
} else {
 lean_dec_ref(x_181);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_173);
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_209 = lean_ctor_get(x_174, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_174, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_211 = x_174;
} else {
 lean_dec_ref(x_174);
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
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_169);
lean_dec(x_63);
x_213 = lean_ctor_get(x_170, 1);
lean_inc(x_213);
lean_dec(x_170);
x_214 = lean_ctor_get(x_171, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_215 = x_171;
} else {
 lean_dec_ref(x_171);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_2, 0);
lean_inc(x_216);
lean_dec(x_2);
lean_inc(x_216);
x_217 = l_Lean_mkHole(x_216);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_217);
x_219 = lean_ctor_get(x_14, 1);
lean_inc(x_219);
lean_inc(x_3);
x_220 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_214);
x_221 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_3);
lean_ctor_set(x_221, 2, x_219);
lean_ctor_set(x_221, 3, x_214);
lean_ctor_set(x_221, 4, x_5);
x_222 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_224, x_12, x_13, x_14, x_15, x_16, x_17, x_213);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_227 = x_225;
} else {
 lean_dec_ref(x_225);
 x_227 = lean_box(0);
}
lean_inc(x_214);
x_228 = l_Lean_Expr_app___override(x_6, x_214);
x_229 = lean_expr_instantiate1(x_64, x_214);
lean_dec(x_64);
if (lean_is_scalar(x_215)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_215;
}
lean_ctor_set(x_230, 0, x_214);
x_231 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_231, 0, x_216);
lean_ctor_set(x_231, 1, x_7);
lean_ctor_set(x_231, 2, x_218);
lean_ctor_set(x_231, 3, x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_8);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_9);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_229);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_228);
lean_ctor_set(x_235, 1, x_234);
if (lean_is_scalar(x_227)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_227;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_226);
return x_236;
}
}
}
default: 
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_1, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_1, 2);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_240 = l_Lean_Expr_getAutoParamTactic_x3f(x_237);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; uint8_t x_242; 
lean_dec(x_10);
x_241 = 3;
x_242 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_239, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_243 = lean_ctor_get(x_2, 0);
lean_inc(x_243);
lean_dec(x_2);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_237);
x_245 = lean_ctor_get(x_16, 5);
lean_inc(x_245);
x_246 = l_Lean_replaceRef(x_243, x_245);
lean_dec(x_245);
x_247 = lean_ctor_get(x_16, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_16, 1);
lean_inc(x_248);
x_249 = lean_ctor_get(x_16, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_16, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_16, 4);
lean_inc(x_251);
x_252 = lean_ctor_get(x_16, 6);
lean_inc(x_252);
x_253 = lean_ctor_get(x_16, 7);
lean_inc(x_253);
x_254 = lean_ctor_get(x_16, 8);
lean_inc(x_254);
x_255 = lean_ctor_get(x_16, 9);
lean_inc(x_255);
x_256 = lean_ctor_get(x_16, 10);
lean_inc(x_256);
x_257 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_257, 0, x_247);
lean_ctor_set(x_257, 1, x_248);
lean_ctor_set(x_257, 2, x_249);
lean_ctor_set(x_257, 3, x_250);
lean_ctor_set(x_257, 4, x_251);
lean_ctor_set(x_257, 5, x_246);
lean_ctor_set(x_257, 6, x_252);
lean_ctor_set(x_257, 7, x_253);
lean_ctor_set(x_257, 8, x_254);
lean_ctor_set(x_257, 9, x_255);
lean_ctor_set(x_257, 10, x_256);
x_258 = 0;
x_259 = lean_box(0);
lean_inc(x_14);
x_260 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_244, x_258, x_259, x_14, x_15, x_257, x_17, x_18);
lean_dec(x_257);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_261);
x_264 = lean_ctor_get(x_14, 1);
lean_inc(x_264);
lean_inc(x_3);
x_265 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_263);
x_266 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_3);
lean_ctor_set(x_266, 2, x_264);
lean_ctor_set(x_266, 3, x_263);
lean_ctor_set(x_266, 4, x_5);
x_267 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_267, 0, x_266);
x_268 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_269, x_12, x_13, x_14, x_15, x_16, x_17, x_262);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_272 = lean_ctor_get(x_270, 0);
lean_dec(x_272);
lean_inc(x_263);
x_273 = l_Lean_Expr_app___override(x_6, x_263);
x_274 = lean_expr_instantiate1(x_238, x_263);
lean_dec(x_238);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_263);
x_276 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_276, 0, x_243);
lean_ctor_set(x_276, 1, x_7);
lean_ctor_set(x_276, 2, x_19);
lean_ctor_set(x_276, 3, x_275);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_8);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_9);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_274);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_273);
lean_ctor_set(x_280, 1, x_279);
lean_ctor_set(x_270, 0, x_280);
return x_270;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_281 = lean_ctor_get(x_270, 1);
lean_inc(x_281);
lean_dec(x_270);
lean_inc(x_263);
x_282 = l_Lean_Expr_app___override(x_6, x_263);
x_283 = lean_expr_instantiate1(x_238, x_263);
lean_dec(x_238);
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_263);
x_285 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_285, 0, x_243);
lean_ctor_set(x_285, 1, x_7);
lean_ctor_set(x_285, 2, x_19);
lean_ctor_set(x_285, 3, x_284);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_8);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_9);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_283);
lean_ctor_set(x_288, 1, x_287);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_282);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_281);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_291 = lean_ctor_get(x_2, 0);
lean_inc(x_291);
lean_dec(x_2);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_237);
x_293 = lean_ctor_get(x_16, 5);
lean_inc(x_293);
x_294 = l_Lean_replaceRef(x_291, x_293);
lean_dec(x_293);
x_295 = lean_ctor_get(x_16, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_16, 1);
lean_inc(x_296);
x_297 = lean_ctor_get(x_16, 2);
lean_inc(x_297);
x_298 = lean_ctor_get(x_16, 3);
lean_inc(x_298);
x_299 = lean_ctor_get(x_16, 4);
lean_inc(x_299);
x_300 = lean_ctor_get(x_16, 6);
lean_inc(x_300);
x_301 = lean_ctor_get(x_16, 7);
lean_inc(x_301);
x_302 = lean_ctor_get(x_16, 8);
lean_inc(x_302);
x_303 = lean_ctor_get(x_16, 9);
lean_inc(x_303);
x_304 = lean_ctor_get(x_16, 10);
lean_inc(x_304);
x_305 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_305, 0, x_295);
lean_ctor_set(x_305, 1, x_296);
lean_ctor_set(x_305, 2, x_297);
lean_ctor_set(x_305, 3, x_298);
lean_ctor_set(x_305, 4, x_299);
lean_ctor_set(x_305, 5, x_294);
lean_ctor_set(x_305, 6, x_300);
lean_ctor_set(x_305, 7, x_301);
lean_ctor_set(x_305, 8, x_302);
lean_ctor_set(x_305, 9, x_303);
lean_ctor_set(x_305, 10, x_304);
x_306 = 1;
x_307 = lean_box(0);
lean_inc(x_14);
x_308 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_292, x_306, x_307, x_14, x_15, x_305, x_17, x_18);
lean_dec(x_305);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_309);
x_311 = l_Lean_Expr_mvarId_x21(x_309);
x_312 = lean_array_push(x_9, x_311);
x_313 = lean_ctor_get(x_14, 1);
lean_inc(x_313);
lean_inc(x_3);
x_314 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_309);
x_315 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_3);
lean_ctor_set(x_315, 2, x_313);
lean_ctor_set(x_315, 3, x_309);
lean_ctor_set(x_315, 4, x_5);
x_316 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_316, 0, x_315);
x_317 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_318, x_12, x_13, x_14, x_15, x_16, x_17, x_310);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_320 = !lean_is_exclusive(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_321 = lean_ctor_get(x_319, 0);
lean_dec(x_321);
lean_inc(x_309);
x_322 = l_Lean_Expr_app___override(x_6, x_309);
x_323 = lean_expr_instantiate1(x_238, x_309);
lean_dec(x_238);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_309);
x_325 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_325, 0, x_291);
lean_ctor_set(x_325, 1, x_7);
lean_ctor_set(x_325, 2, x_19);
lean_ctor_set(x_325, 3, x_324);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_8);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_312);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_323);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_328);
lean_ctor_set(x_319, 0, x_329);
return x_319;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_330 = lean_ctor_get(x_319, 1);
lean_inc(x_330);
lean_dec(x_319);
lean_inc(x_309);
x_331 = l_Lean_Expr_app___override(x_6, x_309);
x_332 = lean_expr_instantiate1(x_238, x_309);
lean_dec(x_238);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_309);
x_334 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_334, 0, x_291);
lean_ctor_set(x_334, 1, x_7);
lean_ctor_set(x_334, 2, x_19);
lean_ctor_set(x_334, 3, x_333);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_8);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_312);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_332);
lean_ctor_set(x_337, 1, x_336);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_331);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_330);
return x_339;
}
}
}
else
{
uint8_t x_340; 
x_340 = !lean_is_exclusive(x_240);
if (x_340 == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_240, 0);
if (lean_obj_tag(x_341) == 4)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_ctor_get(x_16, 2);
lean_inc(x_343);
x_344 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_10, x_343, x_342);
lean_dec(x_343);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_free_object(x_240);
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
lean_dec(x_344);
x_346 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_347 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_347, 0, x_346);
x_348 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_347, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_348;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; 
x_349 = lean_ctor_get(x_344, 0);
lean_inc(x_349);
lean_dec(x_344);
lean_inc(x_16);
x_350 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_16, x_17, x_18);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_st_ref_get(x_17, x_352);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
x_355 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6;
x_356 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_356, 0, x_351);
lean_ctor_set(x_356, 1, x_355);
x_357 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_358 = lean_array_push(x_357, x_356);
x_359 = lean_array_push(x_358, x_349);
x_360 = lean_box(2);
x_361 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5;
x_362 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
lean_ctor_set(x_362, 2, x_359);
x_363 = lean_unsigned_to_nat(0u);
x_364 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_237, x_363);
x_365 = lean_nat_sub(x_364, x_363);
lean_dec(x_364);
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_nat_sub(x_365, x_366);
lean_dec(x_365);
x_368 = l_Lean_Expr_getRevArg_x21(x_237, x_367);
x_369 = lean_expr_consume_type_annotations(x_368);
lean_ctor_set(x_240, 0, x_369);
x_370 = lean_box(0);
x_371 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_372 = l_Lean_Elab_Term_elabTermEnsuringType(x_362, x_240, x_371, x_371, x_370, x_12, x_13, x_14, x_15, x_16, x_17, x_354);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_372, 1);
lean_inc(x_374);
lean_dec(x_372);
x_375 = lean_ctor_get(x_14, 1);
lean_inc(x_375);
lean_inc(x_3);
x_376 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_373);
x_377 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_3);
lean_ctor_set(x_377, 2, x_375);
lean_ctor_set(x_377, 3, x_373);
lean_ctor_set(x_377, 4, x_5);
x_378 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_378, 0, x_377);
x_379 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_380, x_12, x_13, x_14, x_15, x_16, x_17, x_374);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_383 = lean_ctor_get(x_381, 0);
lean_dec(x_383);
lean_inc(x_373);
x_384 = l_Lean_Expr_app___override(x_6, x_373);
x_385 = lean_expr_instantiate1(x_238, x_373);
lean_dec(x_238);
x_386 = lean_ctor_get(x_2, 0);
lean_inc(x_386);
lean_dec(x_2);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_373);
x_388 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_7);
lean_ctor_set(x_388, 2, x_19);
lean_ctor_set(x_388, 3, x_387);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_8);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_9);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_385);
lean_ctor_set(x_391, 1, x_390);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_384);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_381, 0, x_392);
return x_381;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_393 = lean_ctor_get(x_381, 1);
lean_inc(x_393);
lean_dec(x_381);
lean_inc(x_373);
x_394 = l_Lean_Expr_app___override(x_6, x_373);
x_395 = lean_expr_instantiate1(x_238, x_373);
lean_dec(x_238);
x_396 = lean_ctor_get(x_2, 0);
lean_inc(x_396);
lean_dec(x_2);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_373);
x_398 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_7);
lean_ctor_set(x_398, 2, x_19);
lean_ctor_set(x_398, 3, x_397);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_8);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_9);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_395);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_394);
lean_ctor_set(x_402, 1, x_401);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_402);
lean_ctor_set(x_403, 1, x_393);
return x_403;
}
}
else
{
uint8_t x_404; 
lean_dec(x_238);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_404 = !lean_is_exclusive(x_372);
if (x_404 == 0)
{
return x_372;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_372, 0);
x_406 = lean_ctor_get(x_372, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_372);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_405);
lean_ctor_set(x_407, 1, x_406);
return x_407;
}
}
}
}
else
{
uint8_t x_408; uint8_t x_409; 
lean_dec(x_341);
lean_dec(x_10);
x_408 = 3;
x_409 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_239, x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
x_410 = lean_ctor_get(x_2, 0);
lean_inc(x_410);
lean_dec(x_2);
lean_ctor_set(x_240, 0, x_237);
x_411 = lean_ctor_get(x_16, 5);
lean_inc(x_411);
x_412 = l_Lean_replaceRef(x_410, x_411);
lean_dec(x_411);
x_413 = lean_ctor_get(x_16, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_16, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_16, 2);
lean_inc(x_415);
x_416 = lean_ctor_get(x_16, 3);
lean_inc(x_416);
x_417 = lean_ctor_get(x_16, 4);
lean_inc(x_417);
x_418 = lean_ctor_get(x_16, 6);
lean_inc(x_418);
x_419 = lean_ctor_get(x_16, 7);
lean_inc(x_419);
x_420 = lean_ctor_get(x_16, 8);
lean_inc(x_420);
x_421 = lean_ctor_get(x_16, 9);
lean_inc(x_421);
x_422 = lean_ctor_get(x_16, 10);
lean_inc(x_422);
x_423 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_423, 0, x_413);
lean_ctor_set(x_423, 1, x_414);
lean_ctor_set(x_423, 2, x_415);
lean_ctor_set(x_423, 3, x_416);
lean_ctor_set(x_423, 4, x_417);
lean_ctor_set(x_423, 5, x_412);
lean_ctor_set(x_423, 6, x_418);
lean_ctor_set(x_423, 7, x_419);
lean_ctor_set(x_423, 8, x_420);
lean_ctor_set(x_423, 9, x_421);
lean_ctor_set(x_423, 10, x_422);
x_424 = 0;
x_425 = lean_box(0);
lean_inc(x_14);
x_426 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_240, x_424, x_425, x_14, x_15, x_423, x_17, x_18);
lean_dec(x_423);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_427);
x_430 = lean_ctor_get(x_14, 1);
lean_inc(x_430);
lean_inc(x_3);
x_431 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_429);
x_432 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_3);
lean_ctor_set(x_432, 2, x_430);
lean_ctor_set(x_432, 3, x_429);
lean_ctor_set(x_432, 4, x_5);
x_433 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_433, 0, x_432);
x_434 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_436 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_435, x_12, x_13, x_14, x_15, x_16, x_17, x_428);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_437 = !lean_is_exclusive(x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_438 = lean_ctor_get(x_436, 0);
lean_dec(x_438);
lean_inc(x_429);
x_439 = l_Lean_Expr_app___override(x_6, x_429);
x_440 = lean_expr_instantiate1(x_238, x_429);
lean_dec(x_238);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_429);
x_442 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_442, 0, x_410);
lean_ctor_set(x_442, 1, x_7);
lean_ctor_set(x_442, 2, x_19);
lean_ctor_set(x_442, 3, x_441);
x_443 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_8);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_9);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_440);
lean_ctor_set(x_445, 1, x_444);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_439);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set(x_436, 0, x_446);
return x_436;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_447 = lean_ctor_get(x_436, 1);
lean_inc(x_447);
lean_dec(x_436);
lean_inc(x_429);
x_448 = l_Lean_Expr_app___override(x_6, x_429);
x_449 = lean_expr_instantiate1(x_238, x_429);
lean_dec(x_238);
x_450 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_450, 0, x_429);
x_451 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_451, 0, x_410);
lean_ctor_set(x_451, 1, x_7);
lean_ctor_set(x_451, 2, x_19);
lean_ctor_set(x_451, 3, x_450);
x_452 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_8);
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_452);
lean_ctor_set(x_453, 1, x_9);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_449);
lean_ctor_set(x_454, 1, x_453);
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_448);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_447);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; 
x_457 = lean_ctor_get(x_2, 0);
lean_inc(x_457);
lean_dec(x_2);
lean_ctor_set(x_240, 0, x_237);
x_458 = lean_ctor_get(x_16, 5);
lean_inc(x_458);
x_459 = l_Lean_replaceRef(x_457, x_458);
lean_dec(x_458);
x_460 = lean_ctor_get(x_16, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_16, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_16, 2);
lean_inc(x_462);
x_463 = lean_ctor_get(x_16, 3);
lean_inc(x_463);
x_464 = lean_ctor_get(x_16, 4);
lean_inc(x_464);
x_465 = lean_ctor_get(x_16, 6);
lean_inc(x_465);
x_466 = lean_ctor_get(x_16, 7);
lean_inc(x_466);
x_467 = lean_ctor_get(x_16, 8);
lean_inc(x_467);
x_468 = lean_ctor_get(x_16, 9);
lean_inc(x_468);
x_469 = lean_ctor_get(x_16, 10);
lean_inc(x_469);
x_470 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_470, 0, x_460);
lean_ctor_set(x_470, 1, x_461);
lean_ctor_set(x_470, 2, x_462);
lean_ctor_set(x_470, 3, x_463);
lean_ctor_set(x_470, 4, x_464);
lean_ctor_set(x_470, 5, x_459);
lean_ctor_set(x_470, 6, x_465);
lean_ctor_set(x_470, 7, x_466);
lean_ctor_set(x_470, 8, x_467);
lean_ctor_set(x_470, 9, x_468);
lean_ctor_set(x_470, 10, x_469);
x_471 = 1;
x_472 = lean_box(0);
lean_inc(x_14);
x_473 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_240, x_471, x_472, x_14, x_15, x_470, x_17, x_18);
lean_dec(x_470);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
lean_inc(x_474);
x_476 = l_Lean_Expr_mvarId_x21(x_474);
x_477 = lean_array_push(x_9, x_476);
x_478 = lean_ctor_get(x_14, 1);
lean_inc(x_478);
lean_inc(x_3);
x_479 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_474);
x_480 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_3);
lean_ctor_set(x_480, 2, x_478);
lean_ctor_set(x_480, 3, x_474);
lean_ctor_set(x_480, 4, x_5);
x_481 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_482 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
x_484 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_483, x_12, x_13, x_14, x_15, x_16, x_17, x_475);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_485 = !lean_is_exclusive(x_484);
if (x_485 == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_486 = lean_ctor_get(x_484, 0);
lean_dec(x_486);
lean_inc(x_474);
x_487 = l_Lean_Expr_app___override(x_6, x_474);
x_488 = lean_expr_instantiate1(x_238, x_474);
lean_dec(x_238);
x_489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_489, 0, x_474);
x_490 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_490, 0, x_457);
lean_ctor_set(x_490, 1, x_7);
lean_ctor_set(x_490, 2, x_19);
lean_ctor_set(x_490, 3, x_489);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_8);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_491);
lean_ctor_set(x_492, 1, x_477);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_488);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_487);
lean_ctor_set(x_494, 1, x_493);
lean_ctor_set(x_484, 0, x_494);
return x_484;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_495 = lean_ctor_get(x_484, 1);
lean_inc(x_495);
lean_dec(x_484);
lean_inc(x_474);
x_496 = l_Lean_Expr_app___override(x_6, x_474);
x_497 = lean_expr_instantiate1(x_238, x_474);
lean_dec(x_238);
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_474);
x_499 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_499, 0, x_457);
lean_ctor_set(x_499, 1, x_7);
lean_ctor_set(x_499, 2, x_19);
lean_ctor_set(x_499, 3, x_498);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_8);
x_501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_501, 0, x_500);
lean_ctor_set(x_501, 1, x_477);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_497);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_496);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_495);
return x_504;
}
}
}
}
else
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_240, 0);
lean_inc(x_505);
lean_dec(x_240);
if (lean_obj_tag(x_505) == 4)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
lean_dec(x_505);
x_507 = lean_ctor_get(x_16, 2);
lean_inc(x_507);
x_508 = l___private_Lean_Elab_Util_0__Lean_Elab_evalSyntaxConstantUnsafe(x_10, x_507, x_506);
lean_dec(x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
lean_dec(x_508);
x_510 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_511 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_511, 0, x_510);
x_512 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_511, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; 
x_513 = lean_ctor_get(x_508, 0);
lean_inc(x_513);
lean_dec(x_508);
lean_inc(x_16);
x_514 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_exprToSyntax___spec__1___rarg(x_16, x_17, x_18);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = lean_st_ref_get(x_17, x_516);
x_518 = lean_ctor_get(x_517, 1);
lean_inc(x_518);
lean_dec(x_517);
x_519 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6;
x_520 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_520, 0, x_515);
lean_ctor_set(x_520, 1, x_519);
x_521 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17;
x_522 = lean_array_push(x_521, x_520);
x_523 = lean_array_push(x_522, x_513);
x_524 = lean_box(2);
x_525 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5;
x_526 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
lean_ctor_set(x_526, 2, x_523);
x_527 = lean_unsigned_to_nat(0u);
x_528 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_237, x_527);
x_529 = lean_nat_sub(x_528, x_527);
lean_dec(x_528);
x_530 = lean_unsigned_to_nat(1u);
x_531 = lean_nat_sub(x_529, x_530);
lean_dec(x_529);
x_532 = l_Lean_Expr_getRevArg_x21(x_237, x_531);
x_533 = lean_expr_consume_type_annotations(x_532);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
x_535 = lean_box(0);
x_536 = 1;
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_537 = l_Lean_Elab_Term_elabTermEnsuringType(x_526, x_534, x_536, x_536, x_535, x_12, x_13, x_14, x_15, x_16, x_17, x_518);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_537, 1);
lean_inc(x_539);
lean_dec(x_537);
x_540 = lean_ctor_get(x_14, 1);
lean_inc(x_540);
lean_inc(x_3);
x_541 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_538);
x_542 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_3);
lean_ctor_set(x_542, 2, x_540);
lean_ctor_set(x_542, 3, x_538);
lean_ctor_set(x_542, 4, x_5);
x_543 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_543, 0, x_542);
x_544 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
x_546 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_545, x_12, x_13, x_14, x_15, x_16, x_17, x_539);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_548 = x_546;
} else {
 lean_dec_ref(x_546);
 x_548 = lean_box(0);
}
lean_inc(x_538);
x_549 = l_Lean_Expr_app___override(x_6, x_538);
x_550 = lean_expr_instantiate1(x_238, x_538);
lean_dec(x_238);
x_551 = lean_ctor_get(x_2, 0);
lean_inc(x_551);
lean_dec(x_2);
x_552 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_552, 0, x_538);
x_553 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_7);
lean_ctor_set(x_553, 2, x_19);
lean_ctor_set(x_553, 3, x_552);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_8);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_9);
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_550);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_549);
lean_ctor_set(x_557, 1, x_556);
if (lean_is_scalar(x_548)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_548;
}
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_547);
return x_558;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_238);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_559 = lean_ctor_get(x_537, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_537, 1);
lean_inc(x_560);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_561 = x_537;
} else {
 lean_dec_ref(x_537);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(1, 2, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_559);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
}
}
else
{
uint8_t x_563; uint8_t x_564; 
lean_dec(x_505);
lean_dec(x_10);
x_563 = 3;
x_564 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_371_(x_239, x_563);
if (x_564 == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_565 = lean_ctor_get(x_2, 0);
lean_inc(x_565);
lean_dec(x_2);
x_566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_566, 0, x_237);
x_567 = lean_ctor_get(x_16, 5);
lean_inc(x_567);
x_568 = l_Lean_replaceRef(x_565, x_567);
lean_dec(x_567);
x_569 = lean_ctor_get(x_16, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_16, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_16, 2);
lean_inc(x_571);
x_572 = lean_ctor_get(x_16, 3);
lean_inc(x_572);
x_573 = lean_ctor_get(x_16, 4);
lean_inc(x_573);
x_574 = lean_ctor_get(x_16, 6);
lean_inc(x_574);
x_575 = lean_ctor_get(x_16, 7);
lean_inc(x_575);
x_576 = lean_ctor_get(x_16, 8);
lean_inc(x_576);
x_577 = lean_ctor_get(x_16, 9);
lean_inc(x_577);
x_578 = lean_ctor_get(x_16, 10);
lean_inc(x_578);
x_579 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_579, 0, x_569);
lean_ctor_set(x_579, 1, x_570);
lean_ctor_set(x_579, 2, x_571);
lean_ctor_set(x_579, 3, x_572);
lean_ctor_set(x_579, 4, x_573);
lean_ctor_set(x_579, 5, x_568);
lean_ctor_set(x_579, 6, x_574);
lean_ctor_set(x_579, 7, x_575);
lean_ctor_set(x_579, 8, x_576);
lean_ctor_set(x_579, 9, x_577);
lean_ctor_set(x_579, 10, x_578);
x_580 = 0;
x_581 = lean_box(0);
lean_inc(x_14);
x_582 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_566, x_580, x_581, x_14, x_15, x_579, x_17, x_18);
lean_dec(x_579);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_582, 1);
lean_inc(x_584);
lean_dec(x_582);
x_585 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_583);
x_586 = lean_ctor_get(x_14, 1);
lean_inc(x_586);
lean_inc(x_3);
x_587 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_585);
x_588 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_588, 0, x_587);
lean_ctor_set(x_588, 1, x_3);
lean_ctor_set(x_588, 2, x_586);
lean_ctor_set(x_588, 3, x_585);
lean_ctor_set(x_588, 4, x_5);
x_589 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_589, 0, x_588);
x_590 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
x_592 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_591, x_12, x_13, x_14, x_15, x_16, x_17, x_584);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_593 = lean_ctor_get(x_592, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_594 = x_592;
} else {
 lean_dec_ref(x_592);
 x_594 = lean_box(0);
}
lean_inc(x_585);
x_595 = l_Lean_Expr_app___override(x_6, x_585);
x_596 = lean_expr_instantiate1(x_238, x_585);
lean_dec(x_238);
x_597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_597, 0, x_585);
x_598 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_598, 0, x_565);
lean_ctor_set(x_598, 1, x_7);
lean_ctor_set(x_598, 2, x_19);
lean_ctor_set(x_598, 3, x_597);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_8);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_9);
x_601 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_601, 0, x_596);
lean_ctor_set(x_601, 1, x_600);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_595);
lean_ctor_set(x_602, 1, x_601);
if (lean_is_scalar(x_594)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_594;
}
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_593);
return x_603;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_604 = lean_ctor_get(x_2, 0);
lean_inc(x_604);
lean_dec(x_2);
x_605 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_605, 0, x_237);
x_606 = lean_ctor_get(x_16, 5);
lean_inc(x_606);
x_607 = l_Lean_replaceRef(x_604, x_606);
lean_dec(x_606);
x_608 = lean_ctor_get(x_16, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_16, 1);
lean_inc(x_609);
x_610 = lean_ctor_get(x_16, 2);
lean_inc(x_610);
x_611 = lean_ctor_get(x_16, 3);
lean_inc(x_611);
x_612 = lean_ctor_get(x_16, 4);
lean_inc(x_612);
x_613 = lean_ctor_get(x_16, 6);
lean_inc(x_613);
x_614 = lean_ctor_get(x_16, 7);
lean_inc(x_614);
x_615 = lean_ctor_get(x_16, 8);
lean_inc(x_615);
x_616 = lean_ctor_get(x_16, 9);
lean_inc(x_616);
x_617 = lean_ctor_get(x_16, 10);
lean_inc(x_617);
x_618 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_618, 0, x_608);
lean_ctor_set(x_618, 1, x_609);
lean_ctor_set(x_618, 2, x_610);
lean_ctor_set(x_618, 3, x_611);
lean_ctor_set(x_618, 4, x_612);
lean_ctor_set(x_618, 5, x_607);
lean_ctor_set(x_618, 6, x_613);
lean_ctor_set(x_618, 7, x_614);
lean_ctor_set(x_618, 8, x_615);
lean_ctor_set(x_618, 9, x_616);
lean_ctor_set(x_618, 10, x_617);
x_619 = 1;
x_620 = lean_box(0);
lean_inc(x_14);
x_621 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_605, x_619, x_620, x_14, x_15, x_618, x_17, x_18);
lean_dec(x_618);
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
lean_inc(x_622);
x_624 = l_Lean_Expr_mvarId_x21(x_622);
x_625 = lean_array_push(x_9, x_624);
x_626 = lean_ctor_get(x_14, 1);
lean_inc(x_626);
lean_inc(x_3);
x_627 = l_Lean_Name_append(x_4, x_3);
lean_dec(x_4);
lean_inc(x_622);
x_628 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_3);
lean_ctor_set(x_628, 2, x_626);
lean_ctor_set(x_628, 3, x_622);
lean_ctor_set(x_628, 4, x_5);
x_629 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_629, 0, x_628);
x_630 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3;
x_631 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_631, 0, x_629);
lean_ctor_set(x_631, 1, x_630);
x_632 = l_Lean_Elab_pushInfoTree___at_Lean_Elab_Term_addDotCompletionInfo___spec__3(x_631, x_12, x_13, x_14, x_15, x_16, x_17, x_623);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
x_633 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_632)) {
 lean_ctor_release(x_632, 0);
 lean_ctor_release(x_632, 1);
 x_634 = x_632;
} else {
 lean_dec_ref(x_632);
 x_634 = lean_box(0);
}
lean_inc(x_622);
x_635 = l_Lean_Expr_app___override(x_6, x_622);
x_636 = lean_expr_instantiate1(x_238, x_622);
lean_dec(x_238);
x_637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_637, 0, x_622);
x_638 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_638, 0, x_604);
lean_ctor_set(x_638, 1, x_7);
lean_ctor_set(x_638, 2, x_19);
lean_ctor_set(x_638, 3, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_8);
x_640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_625);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_636);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_635);
lean_ctor_set(x_642, 1, x_641);
if (lean_is_scalar(x_634)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_634;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_633);
return x_643;
}
}
}
}
}
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_644 = lean_ctor_get(x_2, 0);
lean_inc(x_644);
lean_dec(x_2);
x_645 = l_Lean_indentExpr(x_1);
x_646 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2;
x_647 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_645);
x_648 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_649 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_649, 0, x_647);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_ctor_get(x_16, 5);
lean_inc(x_650);
x_651 = l_Lean_replaceRef(x_644, x_650);
lean_dec(x_650);
lean_dec(x_644);
x_652 = lean_ctor_get(x_16, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_16, 1);
lean_inc(x_653);
x_654 = lean_ctor_get(x_16, 2);
lean_inc(x_654);
x_655 = lean_ctor_get(x_16, 3);
lean_inc(x_655);
x_656 = lean_ctor_get(x_16, 4);
lean_inc(x_656);
x_657 = lean_ctor_get(x_16, 6);
lean_inc(x_657);
x_658 = lean_ctor_get(x_16, 7);
lean_inc(x_658);
x_659 = lean_ctor_get(x_16, 8);
lean_inc(x_659);
x_660 = lean_ctor_get(x_16, 9);
lean_inc(x_660);
x_661 = lean_ctor_get(x_16, 10);
lean_inc(x_661);
lean_dec(x_16);
x_662 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_662, 0, x_652);
lean_ctor_set(x_662, 1, x_653);
lean_ctor_set(x_662, 2, x_654);
lean_ctor_set(x_662, 3, x_655);
lean_ctor_set(x_662, 4, x_656);
lean_ctor_set(x_662, 5, x_651);
lean_ctor_set(x_662, 6, x_657);
lean_ctor_set(x_662, 7, x_658);
lean_ctor_set(x_662, 8, x_659);
lean_ctor_set(x_662, 9, x_660);
lean_ctor_set(x_662, 10, x_661);
x_663 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_3, x_4, x_649, x_12, x_13, x_14, x_15, x_662, x_17, x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
return x_663;
}
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unexpected unexpanded structure field", 37);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabStruct ", 11);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_27, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = x_29;
goto block_23;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
lean_dec(x_3);
x_33 = lean_ctor_get(x_24, 0);
lean_inc(x_33);
lean_dec(x_24);
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_38 = l_Lean_Meta_whnfForall(x_33, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
x_62 = lean_st_ref_get(x_10, x_40);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_63, 3);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get_uint8(x_64, sizeof(void*)*1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = 0;
x_42 = x_67;
x_43 = x_66;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_dec(x_62);
x_69 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_unbox(x_70);
lean_dec(x_70);
x_42 = x_72;
x_43 = x_71;
goto block_61;
}
block_61:
{
if (x_42 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_45 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1(x_39, x_13, x_37, x_2, x_36, x_32, x_26, x_34, x_35, x_1, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
x_15 = x_45;
goto block_23;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_46 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
lean_inc(x_13);
x_47 = l_Lean_Elab_Term_StructInst_formatField(x_46, x_13);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_39);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_39);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_41, x_56, x_5, x_6, x_7, x_8, x_9, x_10, x_43);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_60 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1(x_39, x_13, x_37, x_2, x_36, x_32, x_26, x_34, x_35, x_1, x_58, x_5, x_6, x_7, x_8, x_9, x_10, x_59);
lean_dec(x_58);
x_15 = x_60;
goto block_23;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_26);
lean_dec(x_13);
x_73 = !lean_is_exclusive(x_38);
if (x_73 == 0)
{
x_15 = x_38;
goto block_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_38, 0);
x_75 = lean_ctor_get(x_38, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_38);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_15 = x_76;
goto block_23;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
x_77 = lean_ctor_get(x_13, 0);
lean_inc(x_77);
lean_dec(x_13);
x_78 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_77, x_78, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = x_79;
goto block_23;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_3);
x_80 = lean_ctor_get(x_13, 0);
lean_inc(x_80);
lean_dec(x_13);
x_81 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_80, x_81, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = x_82;
goto block_23;
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_3 = x_16;
x_4 = x_14;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_7, 5);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 5, x_13);
x_14 = lean_st_ref_get(x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_getStructureCtor(x_17, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 3);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_30 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_17, x_18, x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = !lean_is_exclusive(x_30);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_30, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = l_List_reverse___rarg(x_37);
x_40 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_39);
x_41 = l_Lean_Elab_Term_StructInst_Struct_setParams(x_40, x_25);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_dec(x_30);
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_ctor_get(x_33, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = l_List_reverse___rarg(x_45);
x_48 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_47);
x_49 = l_Lean_Elab_Term_StructInst_Struct_setParams(x_48, x_25);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_46);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_25);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_30, 0);
x_54 = lean_ctor_get(x_30, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_30);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_20);
if (x_56 == 0)
{
return x_20;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_20, 0);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
x_62 = lean_ctor_get(x_7, 2);
x_63 = lean_ctor_get(x_7, 3);
x_64 = lean_ctor_get(x_7, 4);
x_65 = lean_ctor_get(x_7, 5);
x_66 = lean_ctor_get(x_7, 6);
x_67 = lean_ctor_get(x_7, 7);
x_68 = lean_ctor_get(x_7, 8);
x_69 = lean_ctor_get(x_7, 9);
x_70 = lean_ctor_get(x_7, 10);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_71 = l_Lean_replaceRef(x_10, x_65);
lean_dec(x_65);
lean_dec(x_10);
x_72 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_61);
lean_ctor_set(x_72, 2, x_62);
lean_ctor_set(x_72, 3, x_63);
lean_ctor_set(x_72, 4, x_64);
lean_ctor_set(x_72, 5, x_71);
lean_ctor_set(x_72, 6, x_66);
lean_ctor_set(x_72, 7, x_67);
lean_ctor_set(x_72, 8, x_68);
lean_ctor_set(x_72, 9, x_69);
lean_ctor_set(x_72, 10, x_70);
x_73 = lean_st_ref_get(x_8, x_9);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_77);
lean_inc(x_76);
x_78 = l_Lean_getStructureCtor(x_76, x_77);
lean_inc(x_8);
lean_inc(x_72);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_79 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(x_78, x_2, x_3, x_4, x_5, x_6, x_72, x_8, x_75);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_80, 3);
lean_inc(x_84);
lean_dec(x_80);
x_85 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_89 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_76, x_77, x_87, x_88, x_3, x_4, x_5, x_6, x_72, x_8, x_81);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_94 = x_89;
} else {
 lean_dec_ref(x_89);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_dec(x_92);
x_98 = l_List_reverse___rarg(x_96);
x_99 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_98);
x_100 = l_Lean_Elab_Term_StructInst_Struct_setParams(x_99, x_84);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_95);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_101, 2, x_97);
if (lean_is_scalar(x_94)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_94;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_93);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_84);
lean_dec(x_1);
x_103 = lean_ctor_get(x_89, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_105 = x_89;
} else {
 lean_dec_ref(x_89);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_72);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = lean_ctor_get(x_79, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_79, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_109 = x_79;
} else {
 lean_dec_ref(x_79);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_19; 
x_19 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_11);
return x_19;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(x_6, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_4 = lean_array_push(x_2, x_3);
x_5 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
x_6 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_max(x_1, x_9);
lean_dec(x_9);
lean_dec(x_1);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_instInhabited___rarg(x_1, x_3);
x_5 = lean_panic_fn(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = l_instInhabited___rarg(x_1, x_3);
x_5 = lean_panic_fn(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg(x_1, x_2, x_3);
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
static lean_object* _init_l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.StructInst.DefaultFields.findDefaultMissing?", 59);
return x_1;
}
}
static lean_object* _init_l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1;
x_3 = lean_unsigned_to_nat(718u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__1), 4, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_11);
x_13 = lean_ctor_get(x_8, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_2);
x_14 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2;
x_15 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__1___rarg(x_1, x_14);
x_16 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_15, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
x_23 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_22, x_12);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
if (lean_obj_tag(x_24) == 2)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_1);
x_26 = l_Lean_MVarId_isAssigned___rarg(x_1, x_2, x_25);
x_27 = lean_alloc_closure((void*)(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_8);
lean_inc(x_10);
x_28 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_26, x_27);
x_29 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_28, x_12);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = lean_apply_2(x_31, lean_box(0), x_32);
x_34 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_33, x_12);
return x_34;
}
}
}
}
case 1:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_8);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
lean_dec(x_11);
x_36 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___rarg(x_1, x_2, x_35);
x_37 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_36, x_12);
return x_37;
}
default: 
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_8, 3);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_2);
x_39 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2;
x_40 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__2___rarg(x_1, x_39);
x_41 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_40, x_12);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_8);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_box(0);
x_47 = lean_apply_2(x_45, lean_box(0), x_46);
x_48 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_47, x_12);
return x_48;
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 0);
lean_inc(x_49);
lean_dec(x_43);
if (lean_obj_tag(x_49) == 2)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_1);
x_51 = l_Lean_MVarId_isAssigned___rarg(x_1, x_2, x_50);
x_52 = lean_alloc_closure((void*)(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2___boxed), 3, 2);
lean_closure_set(x_52, 0, x_1);
lean_closure_set(x_52, 1, x_8);
lean_inc(x_10);
x_53 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_51, x_52);
x_54 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_53, x_12);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_2);
x_55 = lean_ctor_get(x_1, 0);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_apply_2(x_56, lean_box(0), x_57);
x_59 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_58, x_12);
return x_59;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_3);
lean_dec(x_3);
x_5 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___lambda__2(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.StructInst.DefaultFields.getFieldName", 52);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1;
x_3 = lean_unsigned_to_nat(726u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_4 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_9 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_11 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_get(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_12, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_1, 2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
x_28 = lean_box(x_27);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_dec(x_12);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_2);
x_4 = lean_name_eq(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_5 = l_List_findSome_x3f___rarg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_inc(x_6);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
size_t x_11; size_t x_12; 
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
{
size_t _tmp_4 = x_12;
lean_object* _tmp_5 = x_2;
x_5 = _tmp_4;
x_6 = _tmp_5;
}
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_8);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("id", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_15 = l_Lean_BinderInfo_isExplicit(x_13);
if (x_15 == 0)
{
uint8_t x_161; 
x_161 = 0;
x_16 = x_161;
goto block_160;
}
else
{
uint8_t x_162; 
x_162 = 1;
x_16 = x_162;
goto block_160;
}
block_160:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_7, 5);
lean_inc(x_17);
x_18 = l_Lean_replaceRef(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
x_19 = lean_ctor_get(x_7, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_7, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_7, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_7, 10);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_21);
lean_ctor_set(x_29, 3, x_22);
lean_ctor_set(x_29, 4, x_23);
lean_ctor_set(x_29, 5, x_18);
lean_ctor_set(x_29, 6, x_24);
lean_ctor_set(x_29, 7, x_25);
lean_ctor_set(x_29, 8, x_26);
lean_ctor_set(x_29, 9, x_27);
lean_ctor_set(x_29, 10, x_28);
if (x_16 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = l_Lean_Elab_Term_StructInst_Struct_params(x_1);
x_31 = lean_box(0);
x_32 = lean_array_get_size(x_30);
x_33 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1;
x_36 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1(x_10, x_35, x_30, x_33, x_34, x_35);
lean_dec(x_30);
lean_dec(x_10);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4;
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_11);
x_40 = 0;
x_41 = lean_box(0);
lean_inc(x_5);
x_42 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_39, x_40, x_41, x_5, x_6, x_29, x_8, x_9);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_expr_instantiate1(x_12, x_43);
lean_dec(x_43);
lean_dec(x_12);
x_2 = x_45;
x_7 = x_29;
x_9 = x_44;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_48);
x_49 = lean_infer_type(x_48, x_5, x_6, x_29, x_8, x_9);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
x_52 = l_Lean_Meta_isExprDefEq(x_50, x_11, x_5, x_6, x_29, x_8, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
lean_ctor_set(x_52, 0, x_31);
return x_52;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_31);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_expr_instantiate1(x_12, x_48);
lean_dec(x_48);
lean_dec(x_12);
x_2 = x_60;
x_7 = x_29;
x_9 = x_59;
goto _start;
}
}
else
{
uint8_t x_62; 
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
return x_49;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_49, 0);
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_49);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_37);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_37, 0);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_ctor_set(x_37, 0, x_11);
x_72 = 0;
x_73 = lean_box(0);
lean_inc(x_5);
x_74 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_37, x_72, x_73, x_5, x_6, x_29, x_8, x_9);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_expr_instantiate1(x_12, x_75);
lean_dec(x_75);
lean_dec(x_12);
x_2 = x_77;
x_7 = x_29;
x_9 = x_76;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_37);
x_79 = lean_ctor_get(x_71, 0);
lean_inc(x_79);
lean_dec(x_71);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_80);
x_81 = lean_infer_type(x_80, x_5, x_6, x_29, x_8, x_9);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Meta_isExprDefEq(x_82, x_11, x_5, x_6, x_29, x_8, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; 
lean_dec(x_80);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_84, 0);
lean_dec(x_88);
lean_ctor_set(x_84, 0, x_31);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_31);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_expr_instantiate1(x_12, x_80);
lean_dec(x_80);
lean_dec(x_12);
x_2 = x_92;
x_7 = x_29;
x_9 = x_91;
goto _start;
}
}
else
{
uint8_t x_94; 
lean_dec(x_80);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_94 = !lean_is_exclusive(x_84);
if (x_94 == 0)
{
return x_84;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_84, 0);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_84);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_80);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_81);
if (x_98 == 0)
{
return x_81;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_81, 0);
x_100 = lean_ctor_get(x_81, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_81);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_37, 0);
lean_inc(x_102);
lean_dec(x_37);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_11);
x_104 = 0;
x_105 = lean_box(0);
lean_inc(x_5);
x_106 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_103, x_104, x_105, x_5, x_6, x_29, x_8, x_9);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_expr_instantiate1(x_12, x_107);
lean_dec(x_107);
lean_dec(x_12);
x_2 = x_109;
x_7 = x_29;
x_9 = x_108;
goto _start;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
lean_dec(x_102);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_112);
x_113 = lean_infer_type(x_112, x_5, x_6, x_29, x_8, x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
x_116 = l_Lean_Meta_isExprDefEq(x_114, x_11, x_5, x_6, x_29, x_8, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_31);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_dec(x_116);
x_123 = lean_expr_instantiate1(x_12, x_112);
lean_dec(x_112);
lean_dec(x_12);
x_2 = x_123;
x_7 = x_29;
x_9 = x_122;
goto _start;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_116, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_127 = x_116;
} else {
 lean_dec_ref(x_116);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_112);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_129 = lean_ctor_get(x_113, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_113, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_131 = x_113;
} else {
 lean_dec_ref(x_113);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
}
}
}
}
else
{
lean_object* x_133; 
x_133 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_10);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_9);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_133, 0);
lean_inc(x_136);
lean_dec(x_133);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_136);
x_137 = lean_infer_type(x_136, x_5, x_6, x_29, x_8, x_9);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_8);
lean_inc(x_29);
lean_inc(x_6);
lean_inc(x_5);
x_140 = l_Lean_Meta_isExprDefEq(x_138, x_11, x_5, x_6, x_29, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_unbox(x_141);
lean_dec(x_141);
if (x_142 == 0)
{
uint8_t x_143; 
lean_dec(x_136);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_143 = !lean_is_exclusive(x_140);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_140, 0);
lean_dec(x_144);
x_145 = lean_box(0);
lean_ctor_set(x_140, 0, x_145);
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_dec(x_140);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
lean_dec(x_140);
x_150 = lean_expr_instantiate1(x_12, x_136);
lean_dec(x_136);
lean_dec(x_12);
x_2 = x_150;
x_7 = x_29;
x_9 = x_149;
goto _start;
}
}
else
{
uint8_t x_152; 
lean_dec(x_136);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_152 = !lean_is_exclusive(x_140);
if (x_152 == 0)
{
return x_140;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_140, 0);
x_154 = lean_ctor_get(x_140, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_140);
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
lean_dec(x_136);
lean_dec(x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_156 = !lean_is_exclusive(x_137);
if (x_156 == 0)
{
return x_137;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_137, 0);
x_158 = lean_ctor_get(x_137, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_137);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_163 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2;
x_164 = lean_unsigned_to_nat(2u);
x_165 = l_Lean_Expr_isAppOfArity(x_2, x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_2);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_9);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_9);
return x_170;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_7, 5);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 5, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Meta_mkFreshLevelMVarsFor(x_2, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Core_instantiateValueLevelParams(x_2, x_15, x_7, x_8, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 2);
x_24 = lean_ctor_get(x_7, 3);
x_25 = lean_ctor_get(x_7, 4);
x_26 = lean_ctor_get(x_7, 5);
x_27 = lean_ctor_get(x_7, 6);
x_28 = lean_ctor_get(x_7, 7);
x_29 = lean_ctor_get(x_7, 8);
x_30 = lean_ctor_get(x_7, 9);
x_31 = lean_ctor_get(x_7, 10);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_32 = l_Lean_replaceRef(x_10, x_26);
lean_dec(x_26);
lean_dec(x_10);
x_33 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_33, 3, x_24);
lean_ctor_set(x_33, 4, x_25);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_27);
lean_ctor_set(x_33, 7, x_28);
lean_ctor_set(x_33, 8, x_29);
lean_ctor_set(x_33, 9, x_30);
lean_ctor_set(x_33, 10, x_31);
lean_inc(x_8);
lean_inc(x_33);
lean_inc(x_6);
lean_inc(x_5);
x_34 = l_Lean_Meta_mkFreshLevelMVarsFor(x_2, x_5, x_6, x_33, x_8, x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_33);
x_37 = l_Lean_Core_instantiateValueLevelParams(x_2, x_35, x_33, x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_38, x_3, x_4, x_5, x_6, x_33, x_8, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_20 = lean_array_uset(x_14, x_3, x_16);
x_3 = x_19;
x_4 = x_20;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkLambdaFVars(x_2, x_10, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 0;
x_13 = 1;
x_14 = 1;
x_15 = l_Lean_Meta_mkForallFVars(x_2, x_10, x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = l_Lean_Expr_isMVar(x_18);
if (x_19 == 0)
{
lean_free_object(x_9);
x_2 = x_18;
x_7 = x_16;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Expr_isMVar(x_22);
if (x_23 == 0)
{
x_2 = x_22;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Array_contains___at_Lean_findField_x3f___spec__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_reduceProjOf_x3f(x_2, x_27, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Expr_getAppFn(x_26);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_32 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_31, x_3, x_4, x_5, x_6, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_Expr_isLambda(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_36);
x_38 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1;
lean_inc(x_37);
x_39 = lean_mk_array(x_37, x_38);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_37, x_40);
lean_dec(x_37);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_39, x_41);
x_43 = lean_array_get_size(x_42);
x_44 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_45 = 0;
x_46 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(x_1, x_44, x_45, x_42, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = l_Lean_mkAppN(x_33, x_48);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_46, 0);
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_46);
x_52 = l_Lean_mkAppN(x_33, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_33);
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_2, x_58);
x_60 = lean_mk_empty_array_with_capacity(x_59);
lean_dec(x_59);
x_61 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_2, x_60);
x_62 = 0;
x_63 = l_Lean_Expr_betaRev(x_33, x_61, x_62, x_62);
lean_dec(x_61);
x_2 = x_63;
x_7 = x_34;
goto _start;
}
}
else
{
uint8_t x_65; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_32);
if (x_65 == 0)
{
return x_32;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_32, 0);
x_67 = lean_ctor_get(x_32, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_32);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_26);
lean_dec(x_2);
x_69 = lean_ctor_get(x_28, 1);
lean_inc(x_69);
lean_dec(x_28);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
lean_dec(x_29);
x_2 = x_70;
x_7 = x_69;
goto _start;
}
}
else
{
uint8_t x_72; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_28);
if (x_72 == 0)
{
return x_28;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_28, 0);
x_74 = lean_ctor_get(x_28, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_28);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
case 6:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1), 8, 1);
lean_closure_set(x_76, 0, x_1);
x_77 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_76, x_3, x_4, x_5, x_6, x_7);
return x_77;
}
case 7:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2), 8, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_2, x_78, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
case 8:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1), 8, 1);
lean_closure_set(x_80, 0, x_1);
x_81 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_80, x_3, x_4, x_5, x_6, x_7);
return x_81;
}
case 10:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_2, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_inc(x_83);
x_84 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_83, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_87) == 0)
{
size_t x_88; size_t x_89; uint8_t x_90; 
x_88 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_89 = lean_ptr_addr(x_86);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; 
lean_dec(x_2);
x_91 = l_Lean_Expr_mdata___override(x_82, x_86);
lean_ctor_set(x_84, 0, x_91);
return x_84;
}
else
{
lean_dec(x_86);
lean_dec(x_82);
lean_ctor_set(x_84, 0, x_2);
return x_84;
}
}
else
{
uint8_t x_92; 
lean_dec(x_87);
x_92 = l_Lean_Expr_isMVar(x_86);
if (x_92 == 0)
{
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_2);
return x_84;
}
else
{
size_t x_93; size_t x_94; uint8_t x_95; 
x_93 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_94 = lean_ptr_addr(x_86);
x_95 = lean_usize_dec_eq(x_93, x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_2);
x_96 = l_Lean_Expr_mdata___override(x_82, x_86);
lean_ctor_set(x_84, 0, x_96);
return x_84;
}
else
{
lean_dec(x_86);
lean_dec(x_82);
lean_ctor_set(x_84, 0, x_2);
return x_84;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_84, 0);
x_98 = lean_ctor_get(x_84, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_84);
x_99 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_99) == 0)
{
size_t x_100; size_t x_101; uint8_t x_102; 
x_100 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_101 = lean_ptr_addr(x_97);
x_102 = lean_usize_dec_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_2);
x_103 = l_Lean_Expr_mdata___override(x_82, x_97);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_98);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_97);
lean_dec(x_82);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_2);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_99);
x_106 = l_Lean_Expr_isMVar(x_97);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_2);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_98);
return x_107;
}
else
{
size_t x_108; size_t x_109; uint8_t x_110; 
x_108 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_109 = lean_ptr_addr(x_97);
x_110 = lean_usize_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_2);
x_111 = l_Lean_Expr_mdata___override(x_82, x_97);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_98);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_97);
lean_dec(x_82);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_2);
lean_ctor_set(x_113, 1, x_98);
return x_113;
}
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_84);
if (x_114 == 0)
{
return x_84;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_84, 0);
x_116 = lean_ctor_get(x_84, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_84);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 11:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_2, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_2, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_2, 2);
lean_inc(x_120);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_120);
x_121 = l_Lean_Meta_project_x3f(x_120, x_119, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
lean_inc(x_120);
x_124 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_120, x_3, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ptr_addr(x_120);
lean_dec(x_120);
x_128 = lean_ptr_addr(x_126);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; 
lean_dec(x_2);
x_130 = l_Lean_Expr_proj___override(x_118, x_119, x_126);
lean_ctor_set(x_124, 0, x_130);
return x_124;
}
else
{
lean_dec(x_126);
lean_dec(x_119);
lean_dec(x_118);
lean_ctor_set(x_124, 0, x_2);
return x_124;
}
}
else
{
lean_object* x_131; lean_object* x_132; size_t x_133; size_t x_134; uint8_t x_135; 
x_131 = lean_ctor_get(x_124, 0);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_124);
x_133 = lean_ptr_addr(x_120);
lean_dec(x_120);
x_134 = lean_ptr_addr(x_131);
x_135 = lean_usize_dec_eq(x_133, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_2);
x_136 = l_Lean_Expr_proj___override(x_118, x_119, x_131);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_132);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_131);
lean_dec(x_119);
lean_dec(x_118);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_2);
lean_ctor_set(x_138, 1, x_132);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_124);
if (x_139 == 0)
{
return x_124;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_124, 0);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_124);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_2);
x_143 = lean_ctor_get(x_121, 1);
lean_inc(x_143);
lean_dec(x_121);
x_144 = lean_ctor_get(x_122, 0);
lean_inc(x_144);
lean_dec(x_122);
x_2 = x_144;
x_7 = x_143;
goto _start;
}
}
else
{
uint8_t x_146; 
lean_dec(x_120);
lean_dec(x_119);
lean_dec(x_118);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_121);
if (x_146 == 0)
{
return x_121;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_121, 0);
x_148 = lean_ctor_get(x_121, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_121);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
default: 
{
lean_object* x_150; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_2);
lean_ctor_set(x_150, 1, x_7);
return x_150;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_2);
x_4 = 1;
return x_4;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_3, x_7);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_6, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_array_fget(x_1, x_6);
x_22 = lean_st_ref_get(x_13, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_StructInst_Struct_structName(x_21);
lean_inc(x_4);
x_27 = l_Lean_getDefaultFnForField_x3f(x_25, x_26, x_4);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_6, x_28);
lean_dec(x_6);
x_6 = x_29;
x_14 = x_24;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
lean_inc(x_8);
x_32 = l_Lean_getConstInfo___at_Lean_Elab_Term_mkConst___spec__1(x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_st_ref_get(x_13, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_st_ref_get(x_11, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_41 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_21, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
lean_dec(x_33);
lean_dec(x_21);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_st_ref_get(x_13, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_take(x_11, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_40, sizeof(void*)*8);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_ctor_get(x_40, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_40, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_40, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_40, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_40, 5);
lean_inc(x_56);
x_57 = lean_ctor_get(x_40, 6);
lean_inc(x_57);
x_58 = lean_ctor_get(x_40, 7);
lean_inc(x_58);
lean_dec(x_40);
x_59 = !lean_is_exclusive(x_47);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_47, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_49);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_49, 7);
lean_dec(x_62);
x_63 = lean_ctor_get(x_49, 6);
lean_dec(x_63);
x_64 = lean_ctor_get(x_49, 5);
lean_dec(x_64);
x_65 = lean_ctor_get(x_49, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_49, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_49, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_49, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_49, 0);
lean_dec(x_69);
lean_ctor_set(x_49, 7, x_58);
lean_ctor_set(x_49, 6, x_57);
lean_ctor_set(x_49, 5, x_56);
lean_ctor_set(x_49, 4, x_55);
lean_ctor_set(x_49, 3, x_54);
lean_ctor_set(x_49, 2, x_53);
lean_ctor_set(x_49, 1, x_52);
lean_ctor_set(x_49, 0, x_51);
x_70 = lean_st_ref_set(x_11, x_47, x_50);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_6, x_72);
lean_dec(x_6);
x_74 = lean_nat_add(x_7, x_72);
lean_dec(x_7);
x_6 = x_73;
x_7 = x_74;
x_14 = x_71;
goto _start;
}
else
{
uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get_uint8(x_49, sizeof(void*)*8);
lean_dec(x_49);
x_77 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_77, 0, x_51);
lean_ctor_set(x_77, 1, x_52);
lean_ctor_set(x_77, 2, x_53);
lean_ctor_set(x_77, 3, x_54);
lean_ctor_set(x_77, 4, x_55);
lean_ctor_set(x_77, 5, x_56);
lean_ctor_set(x_77, 6, x_57);
lean_ctor_set(x_77, 7, x_58);
lean_ctor_set_uint8(x_77, sizeof(void*)*8, x_76);
lean_ctor_set(x_47, 0, x_77);
x_78 = lean_st_ref_set(x_11, x_47, x_50);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_6, x_80);
lean_dec(x_6);
x_82 = lean_nat_add(x_7, x_80);
lean_dec(x_7);
x_6 = x_81;
x_7 = x_82;
x_14 = x_79;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_47, 1);
x_85 = lean_ctor_get(x_47, 2);
x_86 = lean_ctor_get(x_47, 3);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_47);
x_87 = lean_ctor_get_uint8(x_49, sizeof(void*)*8);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 lean_ctor_release(x_49, 3);
 lean_ctor_release(x_49, 4);
 lean_ctor_release(x_49, 5);
 lean_ctor_release(x_49, 6);
 lean_ctor_release(x_49, 7);
 x_88 = x_49;
} else {
 lean_dec_ref(x_49);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 8, 1);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_51);
lean_ctor_set(x_89, 1, x_52);
lean_ctor_set(x_89, 2, x_53);
lean_ctor_set(x_89, 3, x_54);
lean_ctor_set(x_89, 4, x_55);
lean_ctor_set(x_89, 5, x_56);
lean_ctor_set(x_89, 6, x_57);
lean_ctor_set(x_89, 7, x_58);
lean_ctor_set_uint8(x_89, sizeof(void*)*8, x_87);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_84);
lean_ctor_set(x_90, 2, x_85);
lean_ctor_set(x_90, 3, x_86);
x_91 = lean_st_ref_set(x_11, x_90, x_50);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_6, x_93);
lean_dec(x_6);
x_95 = lean_nat_add(x_7, x_93);
lean_dec(x_7);
x_6 = x_94;
x_7 = x_95;
x_14 = x_92;
goto _start;
}
}
else
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 1);
lean_inc(x_97);
lean_dec(x_46);
x_98 = !lean_is_exclusive(x_40);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_47);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_100 = lean_ctor_get(x_47, 0);
lean_dec(x_100);
x_101 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_101);
lean_ctor_set(x_47, 0, x_40);
x_102 = lean_st_ref_set(x_11, x_47, x_97);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_6, x_104);
lean_dec(x_6);
x_106 = lean_nat_add(x_7, x_104);
lean_dec(x_7);
x_6 = x_105;
x_7 = x_106;
x_14 = x_103;
goto _start;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_47, 1);
x_109 = lean_ctor_get(x_47, 2);
x_110 = lean_ctor_get(x_47, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_47);
x_111 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_111);
x_112 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_112, 0, x_40);
lean_ctor_set(x_112, 1, x_108);
lean_ctor_set(x_112, 2, x_109);
lean_ctor_set(x_112, 3, x_110);
x_113 = lean_st_ref_set(x_11, x_112, x_97);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_6, x_115);
lean_dec(x_6);
x_117 = lean_nat_add(x_7, x_115);
lean_dec(x_7);
x_6 = x_116;
x_7 = x_117;
x_14 = x_114;
goto _start;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_119 = lean_ctor_get(x_40, 0);
x_120 = lean_ctor_get(x_40, 1);
x_121 = lean_ctor_get(x_40, 2);
x_122 = lean_ctor_get(x_40, 3);
x_123 = lean_ctor_get(x_40, 4);
x_124 = lean_ctor_get(x_40, 5);
x_125 = lean_ctor_get(x_40, 6);
x_126 = lean_ctor_get(x_40, 7);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_40);
x_127 = lean_ctor_get(x_47, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_47, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_47, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_130 = x_47;
} else {
 lean_dec_ref(x_47);
 x_130 = lean_box(0);
}
x_131 = 1;
x_132 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_132, 0, x_119);
lean_ctor_set(x_132, 1, x_120);
lean_ctor_set(x_132, 2, x_121);
lean_ctor_set(x_132, 3, x_122);
lean_ctor_set(x_132, 4, x_123);
lean_ctor_set(x_132, 5, x_124);
lean_ctor_set(x_132, 6, x_125);
lean_ctor_set(x_132, 7, x_126);
lean_ctor_set_uint8(x_132, sizeof(void*)*8, x_131);
if (lean_is_scalar(x_130)) {
 x_133 = lean_alloc_ctor(0, 4, 0);
} else {
 x_133 = x_130;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_127);
lean_ctor_set(x_133, 2, x_128);
lean_ctor_set(x_133, 3, x_129);
x_134 = lean_st_ref_set(x_11, x_133, x_97);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_add(x_6, x_136);
lean_dec(x_6);
x_138 = lean_nat_add(x_7, x_136);
lean_dec(x_7);
x_6 = x_137;
x_7 = x_138;
x_14 = x_135;
goto _start;
}
}
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_41, 1);
lean_inc(x_140);
lean_dec(x_41);
x_141 = !lean_is_exclusive(x_42);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_42, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_143 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_2, x_142, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1;
lean_inc(x_144);
x_147 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_146, x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_5);
x_148 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_145);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = lean_ctor_get(x_149, 2);
lean_inc(x_151);
lean_dec(x_149);
lean_ctor_set(x_42, 0, x_151);
x_152 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_153 = l_Lean_Elab_Term_ensureHasType(x_42, x_144, x_152, x_8, x_9, x_10, x_11, x_12, x_13, x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__2(x_5, x_154, x_8, x_9, x_10, x_11, x_12, x_13, x_155);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 0);
lean_dec(x_158);
x_159 = 1;
x_160 = lean_box(x_159);
lean_ctor_set(x_156, 0, x_160);
return x_156;
}
else
{
lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
lean_dec(x_156);
x_162 = 1;
x_163 = lean_box(x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
}
else
{
uint8_t x_165; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_165 = !lean_is_exclusive(x_153);
if (x_165 == 0)
{
return x_153;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_153, 0);
x_167 = lean_ctor_get(x_153, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_153);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_147);
lean_dec(x_144);
lean_free_object(x_42);
x_169 = lean_st_ref_get(x_13, x_145);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_11, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get_uint8(x_40, sizeof(void*)*8);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_ctor_get(x_40, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_40, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_40, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_40, 3);
lean_inc(x_179);
x_180 = lean_ctor_get(x_40, 4);
lean_inc(x_180);
x_181 = lean_ctor_get(x_40, 5);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 6);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 7);
lean_inc(x_183);
lean_dec(x_40);
x_184 = !lean_is_exclusive(x_172);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_172, 0);
lean_dec(x_185);
x_186 = !lean_is_exclusive(x_174);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_187 = lean_ctor_get(x_174, 7);
lean_dec(x_187);
x_188 = lean_ctor_get(x_174, 6);
lean_dec(x_188);
x_189 = lean_ctor_get(x_174, 5);
lean_dec(x_189);
x_190 = lean_ctor_get(x_174, 4);
lean_dec(x_190);
x_191 = lean_ctor_get(x_174, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_174, 2);
lean_dec(x_192);
x_193 = lean_ctor_get(x_174, 1);
lean_dec(x_193);
x_194 = lean_ctor_get(x_174, 0);
lean_dec(x_194);
lean_ctor_set(x_174, 7, x_183);
lean_ctor_set(x_174, 6, x_182);
lean_ctor_set(x_174, 5, x_181);
lean_ctor_set(x_174, 4, x_180);
lean_ctor_set(x_174, 3, x_179);
lean_ctor_set(x_174, 2, x_178);
lean_ctor_set(x_174, 1, x_177);
lean_ctor_set(x_174, 0, x_176);
x_195 = lean_st_ref_set(x_11, x_172, x_175);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_nat_add(x_6, x_197);
lean_dec(x_6);
x_199 = lean_nat_add(x_7, x_197);
lean_dec(x_7);
x_6 = x_198;
x_7 = x_199;
x_14 = x_196;
goto _start;
}
else
{
uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get_uint8(x_174, sizeof(void*)*8);
lean_dec(x_174);
x_202 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_202, 0, x_176);
lean_ctor_set(x_202, 1, x_177);
lean_ctor_set(x_202, 2, x_178);
lean_ctor_set(x_202, 3, x_179);
lean_ctor_set(x_202, 4, x_180);
lean_ctor_set(x_202, 5, x_181);
lean_ctor_set(x_202, 6, x_182);
lean_ctor_set(x_202, 7, x_183);
lean_ctor_set_uint8(x_202, sizeof(void*)*8, x_201);
lean_ctor_set(x_172, 0, x_202);
x_203 = lean_st_ref_set(x_11, x_172, x_175);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_nat_add(x_6, x_205);
lean_dec(x_6);
x_207 = lean_nat_add(x_7, x_205);
lean_dec(x_7);
x_6 = x_206;
x_7 = x_207;
x_14 = x_204;
goto _start;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_209 = lean_ctor_get(x_172, 1);
x_210 = lean_ctor_get(x_172, 2);
x_211 = lean_ctor_get(x_172, 3);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_172);
x_212 = lean_ctor_get_uint8(x_174, sizeof(void*)*8);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 lean_ctor_release(x_174, 2);
 lean_ctor_release(x_174, 3);
 lean_ctor_release(x_174, 4);
 lean_ctor_release(x_174, 5);
 lean_ctor_release(x_174, 6);
 lean_ctor_release(x_174, 7);
 x_213 = x_174;
} else {
 lean_dec_ref(x_174);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(0, 8, 1);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_176);
lean_ctor_set(x_214, 1, x_177);
lean_ctor_set(x_214, 2, x_178);
lean_ctor_set(x_214, 3, x_179);
lean_ctor_set(x_214, 4, x_180);
lean_ctor_set(x_214, 5, x_181);
lean_ctor_set(x_214, 6, x_182);
lean_ctor_set(x_214, 7, x_183);
lean_ctor_set_uint8(x_214, sizeof(void*)*8, x_212);
x_215 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_209);
lean_ctor_set(x_215, 2, x_210);
lean_ctor_set(x_215, 3, x_211);
x_216 = lean_st_ref_set(x_11, x_215, x_175);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
lean_dec(x_216);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_nat_add(x_6, x_218);
lean_dec(x_6);
x_220 = lean_nat_add(x_7, x_218);
lean_dec(x_7);
x_6 = x_219;
x_7 = x_220;
x_14 = x_217;
goto _start;
}
}
else
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_171, 1);
lean_inc(x_222);
lean_dec(x_171);
x_223 = !lean_is_exclusive(x_40);
if (x_223 == 0)
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_172);
if (x_224 == 0)
{
lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_225 = lean_ctor_get(x_172, 0);
lean_dec(x_225);
x_226 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_226);
lean_ctor_set(x_172, 0, x_40);
x_227 = lean_st_ref_set(x_11, x_172, x_222);
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_nat_add(x_6, x_229);
lean_dec(x_6);
x_231 = lean_nat_add(x_7, x_229);
lean_dec(x_7);
x_6 = x_230;
x_7 = x_231;
x_14 = x_228;
goto _start;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_233 = lean_ctor_get(x_172, 1);
x_234 = lean_ctor_get(x_172, 2);
x_235 = lean_ctor_get(x_172, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_172);
x_236 = 1;
lean_ctor_set_uint8(x_40, sizeof(void*)*8, x_236);
x_237 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_237, 0, x_40);
lean_ctor_set(x_237, 1, x_233);
lean_ctor_set(x_237, 2, x_234);
lean_ctor_set(x_237, 3, x_235);
x_238 = lean_st_ref_set(x_11, x_237, x_222);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_nat_add(x_6, x_240);
lean_dec(x_6);
x_242 = lean_nat_add(x_7, x_240);
lean_dec(x_7);
x_6 = x_241;
x_7 = x_242;
x_14 = x_239;
goto _start;
}
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_244 = lean_ctor_get(x_40, 0);
x_245 = lean_ctor_get(x_40, 1);
x_246 = lean_ctor_get(x_40, 2);
x_247 = lean_ctor_get(x_40, 3);
x_248 = lean_ctor_get(x_40, 4);
x_249 = lean_ctor_get(x_40, 5);
x_250 = lean_ctor_get(x_40, 6);
x_251 = lean_ctor_get(x_40, 7);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_40);
x_252 = lean_ctor_get(x_172, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_172, 2);
lean_inc(x_253);
x_254 = lean_ctor_get(x_172, 3);
lean_inc(x_254);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_255 = x_172;
} else {
 lean_dec_ref(x_172);
 x_255 = lean_box(0);
}
x_256 = 1;
x_257 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_257, 0, x_244);
lean_ctor_set(x_257, 1, x_245);
lean_ctor_set(x_257, 2, x_246);
lean_ctor_set(x_257, 3, x_247);
lean_ctor_set(x_257, 4, x_248);
lean_ctor_set(x_257, 5, x_249);
lean_ctor_set(x_257, 6, x_250);
lean_ctor_set(x_257, 7, x_251);
lean_ctor_set_uint8(x_257, sizeof(void*)*8, x_256);
if (lean_is_scalar(x_255)) {
 x_258 = lean_alloc_ctor(0, 4, 0);
} else {
 x_258 = x_255;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_252);
lean_ctor_set(x_258, 2, x_253);
lean_ctor_set(x_258, 3, x_254);
x_259 = lean_st_ref_set(x_11, x_258, x_222);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_nat_add(x_6, x_261);
lean_dec(x_6);
x_263 = lean_nat_add(x_7, x_261);
lean_dec(x_7);
x_6 = x_262;
x_7 = x_263;
x_14 = x_260;
goto _start;
}
}
}
}
else
{
uint8_t x_265; 
lean_free_object(x_42);
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_265 = !lean_is_exclusive(x_143);
if (x_265 == 0)
{
return x_143;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_143, 0);
x_267 = lean_ctor_get(x_143, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_143);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_42, 0);
lean_inc(x_269);
lean_dec(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_270 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_2, x_269, x_10, x_11, x_12, x_13, x_140);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
x_273 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1;
lean_inc(x_271);
x_274 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_273, x_271);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_5);
x_275 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_272);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = lean_ctor_get(x_276, 2);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
x_280 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_281 = l_Lean_Elab_Term_ensureHasType(x_279, x_271, x_280, x_8, x_9, x_10, x_11, x_12, x_13, x_277);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = l_Lean_MVarId_assign___at_Lean_Elab_Term_exprToSyntax___spec__2(x_5, x_282, x_8, x_9, x_10, x_11, x_12, x_13, x_283);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_285 = lean_ctor_get(x_284, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_286 = x_284;
} else {
 lean_dec_ref(x_284);
 x_286 = lean_box(0);
}
x_287 = 1;
x_288 = lean_box(x_287);
if (lean_is_scalar(x_286)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_286;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_285);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_281, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_292 = x_281;
} else {
 lean_dec_ref(x_281);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
lean_dec(x_274);
lean_dec(x_271);
x_294 = lean_st_ref_get(x_13, x_272);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_296 = lean_st_ref_take(x_11, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get_uint8(x_40, sizeof(void*)*8);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_296, 1);
lean_inc(x_300);
lean_dec(x_296);
x_301 = lean_ctor_get(x_40, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_40, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_40, 2);
lean_inc(x_303);
x_304 = lean_ctor_get(x_40, 3);
lean_inc(x_304);
x_305 = lean_ctor_get(x_40, 4);
lean_inc(x_305);
x_306 = lean_ctor_get(x_40, 5);
lean_inc(x_306);
x_307 = lean_ctor_get(x_40, 6);
lean_inc(x_307);
x_308 = lean_ctor_get(x_40, 7);
lean_inc(x_308);
lean_dec(x_40);
x_309 = lean_ctor_get(x_297, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_297, 2);
lean_inc(x_310);
x_311 = lean_ctor_get(x_297, 3);
lean_inc(x_311);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 lean_ctor_release(x_297, 3);
 x_312 = x_297;
} else {
 lean_dec_ref(x_297);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get_uint8(x_299, sizeof(void*)*8);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 lean_ctor_release(x_299, 2);
 lean_ctor_release(x_299, 3);
 lean_ctor_release(x_299, 4);
 lean_ctor_release(x_299, 5);
 lean_ctor_release(x_299, 6);
 lean_ctor_release(x_299, 7);
 x_314 = x_299;
} else {
 lean_dec_ref(x_299);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(0, 8, 1);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_301);
lean_ctor_set(x_315, 1, x_302);
lean_ctor_set(x_315, 2, x_303);
lean_ctor_set(x_315, 3, x_304);
lean_ctor_set(x_315, 4, x_305);
lean_ctor_set(x_315, 5, x_306);
lean_ctor_set(x_315, 6, x_307);
lean_ctor_set(x_315, 7, x_308);
lean_ctor_set_uint8(x_315, sizeof(void*)*8, x_313);
if (lean_is_scalar(x_312)) {
 x_316 = lean_alloc_ctor(0, 4, 0);
} else {
 x_316 = x_312;
}
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_309);
lean_ctor_set(x_316, 2, x_310);
lean_ctor_set(x_316, 3, x_311);
x_317 = lean_st_ref_set(x_11, x_316, x_300);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = lean_unsigned_to_nat(1u);
x_320 = lean_nat_add(x_6, x_319);
lean_dec(x_6);
x_321 = lean_nat_add(x_7, x_319);
lean_dec(x_7);
x_6 = x_320;
x_7 = x_321;
x_14 = x_318;
goto _start;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_323 = lean_ctor_get(x_296, 1);
lean_inc(x_323);
lean_dec(x_296);
x_324 = lean_ctor_get(x_40, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_40, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_40, 2);
lean_inc(x_326);
x_327 = lean_ctor_get(x_40, 3);
lean_inc(x_327);
x_328 = lean_ctor_get(x_40, 4);
lean_inc(x_328);
x_329 = lean_ctor_get(x_40, 5);
lean_inc(x_329);
x_330 = lean_ctor_get(x_40, 6);
lean_inc(x_330);
x_331 = lean_ctor_get(x_40, 7);
lean_inc(x_331);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 lean_ctor_release(x_40, 7);
 x_332 = x_40;
} else {
 lean_dec_ref(x_40);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_297, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_297, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_297, 3);
lean_inc(x_335);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 lean_ctor_release(x_297, 2);
 lean_ctor_release(x_297, 3);
 x_336 = x_297;
} else {
 lean_dec_ref(x_297);
 x_336 = lean_box(0);
}
x_337 = 1;
if (lean_is_scalar(x_332)) {
 x_338 = lean_alloc_ctor(0, 8, 1);
} else {
 x_338 = x_332;
}
lean_ctor_set(x_338, 0, x_324);
lean_ctor_set(x_338, 1, x_325);
lean_ctor_set(x_338, 2, x_326);
lean_ctor_set(x_338, 3, x_327);
lean_ctor_set(x_338, 4, x_328);
lean_ctor_set(x_338, 5, x_329);
lean_ctor_set(x_338, 6, x_330);
lean_ctor_set(x_338, 7, x_331);
lean_ctor_set_uint8(x_338, sizeof(void*)*8, x_337);
if (lean_is_scalar(x_336)) {
 x_339 = lean_alloc_ctor(0, 4, 0);
} else {
 x_339 = x_336;
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_333);
lean_ctor_set(x_339, 2, x_334);
lean_ctor_set(x_339, 3, x_335);
x_340 = lean_st_ref_set(x_11, x_339, x_323);
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
lean_dec(x_340);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_nat_add(x_6, x_342);
lean_dec(x_6);
x_344 = lean_nat_add(x_7, x_342);
lean_dec(x_7);
x_6 = x_343;
x_7 = x_344;
x_14 = x_341;
goto _start;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_346 = lean_ctor_get(x_270, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_270, 1);
lean_inc(x_347);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_348 = x_270;
} else {
 lean_dec_ref(x_270);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(1, 2, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_40);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_350 = !lean_is_exclusive(x_41);
if (x_350 == 0)
{
return x_41;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_41, 0);
x_352 = lean_ctor_get(x_41, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_41);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_354 = !lean_is_exclusive(x_32);
if (x_354 == 0)
{
return x_32;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_32, 0);
x_356 = lean_ctor_get(x_32, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_32);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
}
}
else
{
uint8_t x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_358 = 0;
x_359 = lean_box(x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_14);
return x_360;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_1, x_2, x_3, x_4, x_5, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_instMonadTermElabM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1;
x_2 = l_instInhabitedPUnit;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2;
x_2 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_st_ref_take(x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_14 = 1;
lean_ctor_set_uint8(x_9, sizeof(void*)*8, x_14);
x_15 = lean_st_ref_set(x_1, x_8, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
x_24 = lean_ctor_get(x_9, 2);
x_25 = lean_ctor_get(x_9, 3);
x_26 = lean_ctor_get(x_9, 4);
x_27 = lean_ctor_get(x_9, 5);
x_28 = lean_ctor_get(x_9, 6);
x_29 = lean_ctor_get(x_9, 7);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_26);
lean_ctor_set(x_31, 5, x_27);
lean_ctor_set(x_31, 6, x_28);
lean_ctor_set(x_31, 7, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*8, x_30);
lean_ctor_set(x_8, 0, x_31);
x_32 = lean_st_ref_set(x_1, x_8, x_10);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_34 = x_32;
} else {
 lean_dec_ref(x_32);
 x_34 = lean_box(0);
}
x_35 = lean_box(0);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_37 = lean_ctor_get(x_8, 1);
x_38 = lean_ctor_get(x_8, 2);
x_39 = lean_ctor_get(x_8, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_8);
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_9, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_9, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_9, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_9, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_9, 6);
lean_inc(x_46);
x_47 = lean_ctor_get(x_9, 7);
lean_inc(x_47);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 lean_ctor_release(x_9, 3);
 lean_ctor_release(x_9, 4);
 lean_ctor_release(x_9, 5);
 lean_ctor_release(x_9, 6);
 lean_ctor_release(x_9, 7);
 x_48 = x_9;
} else {
 lean_dec_ref(x_9);
 x_48 = lean_box(0);
}
x_49 = 1;
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 8, 1);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_42);
lean_ctor_set(x_50, 3, x_43);
lean_ctor_set(x_50, 4, x_44);
lean_ctor_set(x_50, 5, x_45);
lean_ctor_set(x_50, 6, x_46);
lean_ctor_set(x_50, 7, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*8, x_49);
x_51 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_37);
lean_ctor_set(x_51, 2, x_38);
lean_ctor_set(x_51, 3, x_39);
x_52 = lean_st_ref_set(x_1, x_51, x_10);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_box(0);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg___boxed), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg(x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_7, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_18, 6);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Std_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_19, x_1);
x_21 = lean_box(x_20);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_24, 6);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Std_PersistentHashMap_contains___at_Lean_MVarId_isAssigned___spec__1(x_25, x_1);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Elab.Term.StructInst.DefaultFields.step", 44);
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1;
x_2 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1;
x_3 = lean_unsigned_to_nat(840u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_20 = lean_ctor_get(x_13, 2);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_24;
x_16 = x_23;
goto block_19;
}
else
{
uint8_t x_25; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_20);
x_29 = lean_ctor_get(x_13, 3);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
x_30 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_33;
x_16 = x_32;
goto block_19;
}
else
{
uint8_t x_34; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
x_39 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_38);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
lean_dec(x_13);
x_40 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_40;
x_16 = x_11;
goto block_19;
}
else
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
if (lean_obj_tag(x_41) == 2)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_42);
x_43 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_3, 2);
lean_inc(x_50);
x_51 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_13);
lean_dec(x_13);
x_52 = lean_ctor_get(x_9, 5);
lean_inc(x_52);
x_53 = l_Lean_replaceRef(x_47, x_52);
lean_dec(x_52);
lean_dec(x_47);
x_54 = lean_ctor_get(x_9, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_9, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_9, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_9, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_9, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_9, 7);
lean_inc(x_60);
x_61 = lean_ctor_get(x_9, 8);
lean_inc(x_61);
x_62 = lean_ctor_get(x_9, 9);
lean_inc(x_62);
x_63 = lean_ctor_get(x_9, 10);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set(x_64, 1, x_55);
lean_ctor_set(x_64, 2, x_56);
lean_ctor_set(x_64, 3, x_57);
lean_ctor_set(x_64, 4, x_58);
lean_ctor_set(x_64, 5, x_53);
lean_ctor_set(x_64, 6, x_59);
lean_ctor_set(x_64, 7, x_60);
lean_ctor_set(x_64, 8, x_61);
lean_ctor_set(x_64, 9, x_62);
lean_ctor_set(x_64, 10, x_63);
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_48, x_49, x_50, x_51, x_42, x_65, x_65, x_5, x_6, x_7, x_8, x_64, x_10, x_46);
lean_dec(x_50);
lean_dec(x_48);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_70;
x_16 = x_69;
goto block_19;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_st_ref_get(x_10, x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_st_ref_take(x_4, x_73);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = 1;
x_77 = lean_box(x_76);
x_78 = lean_st_ref_set(x_4, x_77, x_75);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_80;
x_16 = x_79;
goto block_19;
}
}
else
{
uint8_t x_81; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_42);
lean_dec(x_13);
x_85 = lean_ctor_get(x_43, 1);
lean_inc(x_85);
lean_dec(x_43);
x_86 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_86;
x_16 = x_85;
goto block_19;
}
}
else
{
lean_object* x_87; 
lean_dec(x_41);
lean_dec(x_13);
x_87 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3;
x_15 = x_87;
x_16 = x_11;
goto block_19;
}
}
}
}
block_19:
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_1 = x_14;
x_2 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_16 = !lean_is_exclusive(x_2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_push(x_17, x_1);
lean_ctor_set(x_2, 0, x_18);
x_19 = lean_box(0);
x_20 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4(x_15, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_32 = lean_array_push(x_29, x_1);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
x_34 = lean_box(0);
x_35 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4(x_15, x_34, x_33, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_37 = x_35;
} else {
 lean_dec_ref(x_35);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_41 = x_35;
} else {
 lean_dec_ref(x_35);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_11, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_11, 0, x_45);
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_markUsedAssignment___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
static lean_object* _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1;
x_3 = l_instInhabited___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_15 = x_27;
x_16 = x_28;
goto block_23;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_24);
x_33 = lean_ctor_get(x_13, 3);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_13);
x_34 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_15 = x_36;
x_16 = x_37;
goto block_23;
}
else
{
uint8_t x_38; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_inc(x_42);
lean_dec(x_33);
x_43 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec(x_13);
x_44 = lean_box(0);
x_15 = x_44;
x_16 = x_10;
goto block_23;
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_46) == 2)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
lean_ctor_set(x_43, 0, x_13);
x_15 = x_43;
x_16 = x_51;
goto block_23;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_43);
lean_dec(x_13);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_15 = x_53;
x_16 = x_52;
goto block_23;
}
}
else
{
lean_object* x_54; 
lean_free_object(x_43);
lean_dec(x_46);
lean_dec(x_13);
x_54 = lean_box(0);
x_15 = x_54;
x_16 = x_10;
goto block_23;
}
}
else
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
lean_dec(x_43);
if (lean_obj_tag(x_55) == 2)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
x_57 = l_Lean_MVarId_isAssigned___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__2(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_13);
x_15 = x_61;
x_16 = x_60;
goto block_23;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_13);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_box(0);
x_15 = x_63;
x_16 = x_62;
goto block_23;
}
}
else
{
lean_object* x_64; 
lean_dec(x_55);
lean_dec(x_13);
x_64 = lean_box(0);
x_15 = x_64;
x_16 = x_10;
goto block_23;
}
}
}
}
}
block_23:
{
if (lean_obj_tag(x_15) == 0)
{
x_1 = x_14;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
x_12 = l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__3(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 5);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_tag(x_12, 1);
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
lean_inc(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 5);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_dec(x_1);
lean_ctor_set(x_9, 5, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
x_22 = lean_ctor_get(x_9, 6);
x_23 = lean_ctor_get(x_9, 7);
x_24 = lean_ctor_get(x_9, 8);
x_25 = lean_ctor_get(x_9, 9);
x_26 = lean_ctor_get(x_9, 10);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_27 = l_Lean_replaceRef(x_1, x_21);
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_17);
lean_ctor_set(x_28, 2, x_18);
lean_ctor_set(x_28, 3, x_19);
lean_ctor_set(x_28, 4, x_20);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_22);
lean_ctor_set(x_28, 7, x_23);
lean_ctor_set(x_28, 8, x_24);
lean_ctor_set(x_28, 9, x_25);
lean_ctor_set(x_28, 10, x_26);
x_29 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_28, x_10, x_11);
lean_dec(x_10);
lean_dec(x_28);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_traceMsg", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_9, 5);
x_13 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_14);
x_17 = lean_st_ref_take(x_10, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_18, 3);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2;
x_26 = l_Lean_Name_append(x_1, x_25);
x_27 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_27, 0, x_1);
x_28 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_16);
x_33 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_12);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Std_PersistentArray_push___rarg(x_24, x_36);
lean_ctor_set(x_19, 0, x_37);
x_38 = lean_st_ref_set(x_10, x_18, x_20);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
lean_dec(x_19);
x_47 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2;
x_48 = l_Lean_Name_append(x_1, x_47);
x_49 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_49, 0, x_1);
x_50 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_16);
x_55 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_12);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_12);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Std_PersistentArray_push___rarg(x_46, x_58);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_45);
lean_ctor_set(x_18, 3, x_60);
x_61 = lean_st_ref_set(x_10, x_18, x_20);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_66 = lean_ctor_get(x_18, 0);
x_67 = lean_ctor_get(x_18, 1);
x_68 = lean_ctor_get(x_18, 2);
x_69 = lean_ctor_get(x_18, 4);
x_70 = lean_ctor_get(x_18, 5);
x_71 = lean_ctor_get(x_18, 6);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_18);
x_72 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
x_73 = lean_ctor_get(x_19, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_74 = x_19;
} else {
 lean_dec_ref(x_19);
 x_74 = lean_box(0);
}
x_75 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2;
x_76 = l_Lean_Name_append(x_1, x_75);
x_77 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_77, 0, x_1);
x_78 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_16);
x_83 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_12);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_12);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Std_PersistentArray_push___rarg(x_73, x_86);
if (lean_is_scalar(x_74)) {
 x_88 = lean_alloc_ctor(0, 1, 1);
} else {
 x_88 = x_74;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_72);
x_89 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_89, 0, x_66);
lean_ctor_set(x_89, 1, x_67);
lean_ctor_set(x_89, 2, x_68);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_69);
lean_ctor_set(x_89, 5, x_70);
lean_ctor_set(x_89, 6, x_71);
x_90 = lean_st_ref_set(x_10, x_89, x_20);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 2);
x_12 = l_Lean_checkTraceOption(x_11, x_1);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("' is missing", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = lean_nat_dec_lt(x_1, x_2);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_6, 2);
lean_dec(x_17);
lean_inc(x_2);
lean_ctor_set(x_6, 2, x_2);
x_18 = lean_st_ref_get(x_13, x_14);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_7, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_st_ref_set(x_7, x_23, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_26 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_13, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_st_ref_get(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_36 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_35, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_dec(x_30);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_38, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_6, 0);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_6);
lean_inc(x_2);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_2);
x_47 = lean_st_ref_get(x_13, x_14);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_take(x_7, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_st_ref_set(x_7, x_52, x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_46);
lean_inc(x_3);
x_55 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_3, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_13, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_get(x_7, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_2, x_63);
lean_dec(x_2);
x_65 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_64, x_3, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
lean_dec(x_59);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_67, x_3, x_46, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_66);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_46);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_55, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_71 = x_55;
} else {
 lean_dec_ref(x_55);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_4, 0);
lean_inc(x_73);
x_74 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_4);
lean_dec(x_4);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__4(x_73, x_79, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_80;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("propagate [", 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] [field := ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("]: ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
x_51 = lean_st_ref_get(x_11, x_21);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 3);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*1);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = 0;
x_24 = x_56;
x_25 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unbox(x_59);
lean_dec(x_59);
x_24 = x_61;
x_25 = x_60;
goto block_50;
}
block_50:
{
if (x_24 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1(x_1, x_2, x_3, x_22, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_2);
x_28 = l_Nat_repr(x_2);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
lean_inc(x_22);
x_36 = l_Lean_Elab_Term_StructInst_formatField(x_35, x_22);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_3);
x_41 = l_Lean_Elab_Term_StructInst_formatStruct(x_3);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6(x_23, x_45, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1(x_1, x_2, x_3, x_22, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
return x_13;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_1);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(x_1);
x_10 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(x_1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_st_ref_get(x_7, x_8);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_st_mk_ref(x_17, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_7);
lean_inc(x_19);
x_21 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_9, x_12, x_1, x_13, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_7, x_23);
lean_dec(x_7);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_19, x_25);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_22);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_19);
lean_dec(x_7);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_10);
x_11 = l_Lean_Elab_getBetterRef(x_9, x_10);
x_12 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(x_13, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
lean_dec(x_2);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_tag(x_15, 1);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_dec(x_1);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_25 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_15);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_21);
lean_ctor_set(x_26, 8, x_22);
lean_ctor_set(x_26, 9, x_23);
lean_ctor_set(x_26, 10, x_24);
x_27 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3(x_2, x_3, x_4, x_5, x_6, x_26, x_8, x_9);
lean_dec(x_8);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_27;
}
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_unsupportedSyntaxExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg), 1, 0);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_16);
lean_dec(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_20, x_3, x_16);
lean_dec(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_15, x_3, x_22);
lean_dec(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_27, x_3, x_22);
lean_dec(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_34, x_3, x_31);
lean_dec(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at_Lean_Elab_liftMacroM___spec__1(x_40, x_3, x_36);
lean_dec(x_40);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Environment_contains(x_1, x_2);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 5);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 6);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 10);
lean_inc(x_18);
lean_inc(x_12);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1___boxed), 4, 1);
lean_closure_set(x_19, 0, x_12);
lean_inc(x_16);
x_20 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Elab_liftMacroM___spec__2___rarg___boxed), 3, 1);
lean_closure_set(x_20, 0, x_16);
lean_inc(x_12);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2___boxed), 4, 1);
lean_closure_set(x_21, 0, x_12);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_12);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3___boxed), 6, 3);
lean_closure_set(x_22, 0, x_12);
lean_closure_set(x_22, 1, x_16);
lean_closure_set(x_22, 2, x_17);
lean_inc(x_12);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4___boxed), 6, 3);
lean_closure_set(x_23, 0, x_12);
lean_closure_set(x_23, 1, x_16);
lean_closure_set(x_23, 2, x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_get(x_7, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_environment_main_module(x_12);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_18);
lean_ctor_set(x_30, 3, x_13);
lean_ctor_set(x_30, 4, x_14);
lean_ctor_set(x_30, 5, x_15);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_apply_2(x_1, x_30, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_st_ref_take(x_7, x_27);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = !lean_is_exclusive(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_38, 1);
lean_dec(x_41);
lean_ctor_set(x_38, 1, x_36);
x_42 = lean_st_ref_set(x_7, x_38, x_39);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_dec(x_35);
x_45 = l_List_reverse___rarg(x_44);
x_46 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
lean_ctor_set(x_46, 0, x_34);
return x_46;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 2);
x_53 = lean_ctor_get(x_38, 3);
x_54 = lean_ctor_get(x_38, 4);
x_55 = lean_ctor_get(x_38, 5);
x_56 = lean_ctor_get(x_38, 6);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_57 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_36);
lean_ctor_set(x_57, 2, x_52);
lean_ctor_set(x_57, 3, x_53);
lean_ctor_set(x_57, 4, x_54);
lean_ctor_set(x_57, 5, x_55);
lean_ctor_set(x_57, 6, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_39);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_ctor_get(x_35, 1);
lean_inc(x_60);
lean_dec(x_35);
x_61 = l_List_reverse___rarg(x_60);
x_62 = l_List_forM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__3(x_61, x_2, x_3, x_4, x_5, x_6, x_7, x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_34);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_33, 0);
lean_inc(x_66);
lean_dec(x_33);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_maxRecDepthErrorMessage;
x_70 = lean_string_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_68);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__2(x_67, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_68);
x_74 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_74;
}
}
else
{
lean_object* x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg(x_27);
return x_75;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_3);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("before propagate ", 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
lean_dec(x_4);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_12, x_13, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_dec(x_15);
x_34 = lean_st_ref_get(x_10, x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 3);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get_uint8(x_36, sizeof(void*)*1);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = 0;
x_20 = x_39;
x_21 = x_38;
goto block_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
lean_inc(x_3);
x_41 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
x_20 = x_44;
x_21 = x_43;
goto block_33;
}
block_33:
{
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(x_18, x_19, x_17, x_22, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_17);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_17);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_3, x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(x_18, x_19, x_17, x_30, x_5, x_6, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_30);
lean_dec(x_19);
return x_32;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___boxed), 5, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
x_36 = lean_st_ref_get(x_9, x_20);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 3);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 1);
lean_inc(x_40);
lean_dec(x_36);
x_41 = 0;
x_22 = x_41;
x_23 = x_40;
goto block_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__2(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_22 = x_46;
x_23 = x_45;
goto block_35;
}
block_35:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2(x_19, x_2, x_21, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_19);
x_26 = l_Lean_Elab_Term_StructInst_formatStruct(x_19);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryCoe___spec__1(x_21, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2(x_19, x_2, x_21, x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
return x_34;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_18, 0);
x_49 = lean_ctor_get(x_18, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_15);
if (x_51 == 0)
{
return x_15;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_15, 0);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_15);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_11);
if (x_55 == 0)
{
return x_11;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_11, 0);
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_11);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("invalid {...} notation, explicit source is required when using '[<index>] := <value>'", 85);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
else
{
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp(x_1, x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_26 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_synthesizeInst___spec__1(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_box(x_37);
lean_inc(x_36);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTerm___boxed), 11, 4);
lean_closure_set(x_40, 0, x_36);
lean_closure_set(x_40, 1, x_2);
lean_closure_set(x_40, 2, x_38);
lean_closure_set(x_40, 3, x_39);
x_41 = l_Lean_Elab_Term_withMacroExpansion___rarg(x_1, x_36, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
return x_10;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_10, 0);
x_44 = lean_ctor_get(x_10, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_10);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("elabStructInst", 14);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_termElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_5 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Structure instance. `{ x := e, ... }` assigns `e` to field `x`, which may be\ninherited. If `e` is itself a variable called `x`, it can be elided:\n`fun y => { x := 1, y }`.\nA *structure update* of an existing value can be given via `with`:\n`{ point with x := 1 }`.\nThe structure type can be specified if not inferable:\n`{ x := 1, y := 2 : Point }`. ", 348);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1;
x_4 = l_Lean_addBuiltinDocString(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(905u);
x_2 = lean_unsigned_to_nat(30u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(913u);
x_2 = lean_unsigned_to_nat(88u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1;
x_2 = lean_unsigned_to_nat(30u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2;
x_4 = lean_unsigned_to_nat(88u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(905u);
x_2 = lean_unsigned_to_nat(34u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(905u);
x_2 = lean_unsigned_to_nat(48u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4;
x_2 = lean_unsigned_to_nat(34u);
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5;
x_4 = lean_unsigned_to_nat(48u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3;
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7;
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_12069_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FindExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Structure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_App(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Binders(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_StructInst(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Structure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__12);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__13);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__14);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__15);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__16);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__17);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__18);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__19);
l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20 = _init_l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__20);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__4);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__5);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__6);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__7);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__8);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__9);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__10);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__11);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_docString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__3);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__4);
l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___spec__2___closed__5);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__1);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__2);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__3);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__4);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__5);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__6);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__7);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__8);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__9);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__10);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__1___closed__11);
l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1 = _init_l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___lambda__3___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev___closed__3);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_docString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstFieldAbbrev_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__5);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__7);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__8);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__9);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__10);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__11);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__12);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___lambda__1___closed__13);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources_go___closed__1);
l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1 = _init_l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__1);
l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2 = _init_l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwAbortTerm___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSources___spec__2___rarg___closed__2);
l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo___closed__1);
l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo = _init_l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedExplicitSourceInfo);
l_Lean_Elab_Term_StructInst_instInhabitedSource = _init_l_Lean_Elab_Term_StructInst_instInhabitedSource();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedSource);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSourcesWithSyntax___closed__5);
l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1 = _init_l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1();
lean_mark_persistent(l_panic___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__2___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__1);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__2);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__3);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__3___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__7);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__5);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__7);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__8);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__9);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__10);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__11);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__12);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__13);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__14);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__15);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__16);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__17);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__18);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__2___closed__19);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__5);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__7);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__8);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__9);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__10);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__11);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__12);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__13);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__14);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__15);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___lambda__3___closed__16);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___closed__5);
l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1);
l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS = _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS);
l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1 = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__1);
l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2 = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__2);
l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3 = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__3);
l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4 = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldLHS___closed__4);
l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1);
l_Lean_Elab_Term_StructInst_Field_expr_x3f___default = _init_l_Lean_Elab_Term_StructInst_Field_expr_x3f___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_expr_x3f___default);
l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1);
l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1);
l_Lean_Elab_Term_StructInst_instInhabitedStruct = _init_l_Lean_Elab_Term_StructInst_instInhabitedStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedStruct);
l_Lean_Elab_Term_StructInst_formatField___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__1);
l_Lean_Elab_Term_StructInst_formatField___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__2);
l_Lean_Elab_Term_StructInst_formatField___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__3);
l_Lean_Elab_Term_StructInst_formatField___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__4);
l_Lean_Elab_Term_StructInst_formatField___closed__5 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__5);
l_Lean_Elab_Term_StructInst_formatField___closed__6 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__6);
l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1 = _init_l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1();
lean_mark_persistent(l_List_mapTRAux___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__1);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__2);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__3);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__4);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__5);
l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6 = _init_l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6();
lean_mark_persistent(l_List_format___at_Lean_Elab_Term_StructInst_formatStruct___spec__3___closed__6);
l_Lean_Elab_Term_StructInst_formatStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__2);
l_Lean_Elab_Term_StructInst_formatStruct___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__3);
l_Lean_Elab_Term_StructInst_formatStruct___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__4);
l_Lean_Elab_Term_StructInst_formatStruct___closed__5 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__5);
l_Lean_Elab_Term_StructInst_formatStruct___closed__6 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__6);
l_Lean_Elab_Term_StructInst_formatStruct___closed__7 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__7();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__7);
l_Lean_Elab_Term_StructInst_formatStruct___closed__8 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__8();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__8);
l_Lean_Elab_Term_StructInst_formatStruct___closed__9 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__9();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__9);
l_Lean_Elab_Term_StructInst_instToFormatStruct = _init_l_Lean_Elab_Term_StructInst_instToFormatStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatStruct);
l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1);
l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2 = _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringStruct___closed__2);
l_Lean_Elab_Term_StructInst_instToStringStruct = _init_l_Lean_Elab_Term_StructInst_instToStringStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringStruct);
l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1);
l_Lean_Elab_Term_StructInst_instToFormatFieldStruct = _init_l_Lean_Elab_Term_StructInst_instToFormatFieldStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatFieldStruct);
l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1);
l_Lean_Elab_Term_StructInst_instToStringFieldStruct = _init_l_Lean_Elab_Term_StructInst_instToStringFieldStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringFieldStruct);
l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1 = _init_l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__1);
l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2 = _init_l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___closed__2);
l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1 = _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1);
l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2 = _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2);
l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1);
l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2 = _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6);
l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1 = _init_l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1);
l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2 = _init_l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2();
lean_mark_persistent(l_List_mapTRAux___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__1);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__3);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__4);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__5);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__6);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__7);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__3___closed__8);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__1);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__2);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__3);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__4);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__5);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__13___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___spec__8___closed__1);
l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___spec__3___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2);
l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1 = _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1);
l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2 = _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4);
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__1);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__2);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__3);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__4);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__5);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___lambda__1___closed__6);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__1);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__2);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__3);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default);
l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default();
l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1 = _init_l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1();
lean_mark_persistent(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__1);
l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2 = _init_l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2();
lean_mark_persistent(l_List_findSomeM_x3f___at_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___spec__3___rarg___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__3);
l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___closed__4);
l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1);
l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1 = _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__1);
l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2 = _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__2);
l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3 = _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___closed__3);
l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__1);
l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__2);
l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3 = _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__4___closed__3);
l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1 = _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__1);
l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2 = _init_l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2();
lean_mark_persistent(l_panic___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___closed__2);
l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1 = _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__1);
l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2 = _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__2);
l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3 = _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__3);
l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4 = _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__4);
l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5 = _init_l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__6___closed__5);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___lambda__1___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__3);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__4);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__5);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__6);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__1);
l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__4___closed__2);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__1);
l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2 = _init_l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_throwUnsupportedSyntax___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__5___rarg___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__2___closed__2);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__4);
res = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_docString(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__1);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__2);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__4);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__5);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__6);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange___closed__7);
res = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst_declRange(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_12069_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
