// Lean compiler output
// Module: Lean.Elab.StructInst
// Imports: Init Lean.Util.FindExpr Lean.Parser.Term Lean.Elab.App Lean.Elab.Binders
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
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(lean_object*, lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
uint8_t l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3;
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_expr_x3f___default;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__2(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax_match__1(lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__2(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_instToFormatStruct;
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(lean_object*, lean_object*);
uint8_t l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f_match__1(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12262____closed__10;
lean_object* l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_6666_(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7;
lean_object* l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__2(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Monad_seqRight___default___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__2(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToStringFieldStruct___closed__1;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(lean_object*);
extern lean_object* l_instReprSigma___rarg___closed__1;
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___boxed(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__4(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkId___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__12;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13781____closed__9;
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__1(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedStruct;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__6(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_5935____closed__4;
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_265____closed__6;
lean_object* l_Std_HashMap_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13781____closed__8;
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__6;
extern lean_object* l_Lean_Elab_MacroExpansionInfo_format___closed__3;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDefinition_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1(lean_object*);
extern lean_object* l_Std_Format_sbracket___closed__4;
lean_object* l_Std_Format_joinSep___at_instReprProd___spec__1(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4___boxed(lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeAppInstMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15;
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedStruct___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__1(lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13;
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(lean_object*);
extern lean_object* l_Lean_Json_render___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MetavarContext_isExprAssigned(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_265____closed__2;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1(lean_object*);
lean_object* l_Lean_Meta_project_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12262____closed__12;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct;
lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM_match__1(lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__2;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__7(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__4(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToStringFieldStruct;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17;
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldStruct;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
lean_object* l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__4(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_14350____closed__4;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__8___rarg(lean_object*, lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object*);
lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__5(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___rarg(lean_object*, lean_object*);
extern lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2;
lean_object* l_List_findSome_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__2(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_addMacroStack___at_Lean_Elab_Term_instAddErrorMessageContextTermElabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__1(lean_object*);
uint8_t l_Array_contains___at_Lean_findField_x3f___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_CtorHeaderResult_instMVars___default;
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__2(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2117____closed__4;
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__2(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__7___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3;
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1;
lean_object* l_Lean_Meta_synthInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__3;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12262____closed__9;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields_match__1(lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2;
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__3(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1;
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_Syntax_mkAntiquotNode___closed__9;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1;
extern lean_object* l_Std_Format_sbracket___closed__3;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__1(lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12262____closed__13;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatField_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__4(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource_match__1(lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__3(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__2(lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Array_mapMUnsafe_map___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2;
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields_match__1___rarg(lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS(lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_instToStringSyntax___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(size_t, size_t, lean_object*);
lean_object* l_Std_fmt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__2(lean_object*);
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__1(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__1(lean_object*);
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
uint8_t l_Lean_Expr_isMVar(lean_object*);
extern lean_object* l_Id_instMonadId;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_instInhabitedReaderT___rarg___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__1(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_12262____closed__8;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1;
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__3(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__2(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__2(lean_object*);
lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_adaptExpander___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__3;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__2(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__2(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__3___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__2;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__3(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax_match__1(lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7;
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3;
extern lean_object* l_prec_x28___x29___closed__7;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(lean_object*);
extern lean_object* l_Lean_Parser_Tactic_changeWith___closed__3;
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_findField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5;
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName_match__1(lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_prec_x28___x29___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___closed__1;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__3(lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1080____closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS_match__1(lean_object*);
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source_match__1___rarg(lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__2(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__4;
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__4___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Json_render___closed__7;
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__2(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedPUnit;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref_match__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__8(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2;
lean_object* l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple_match__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedSource;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS_match__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3;
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2;
uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__3;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1;
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1;
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_mkOptionalNode___closed__1;
x_10 = l_Lean_Syntax_setArg(x_1, x_4, x_9);
x_11 = l_Lean_MonadRef_mkInfoFromRefPos___at_myMacro____x40_Init_Notation___hyg_109____spec__1(x_2, x_3);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = l_prec_x28___x29___closed__3;
lean_inc(x_13);
x_15 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Array_empty___closed__1;
x_17 = lean_array_push(x_16, x_15);
x_18 = lean_array_push(x_16, x_10);
x_19 = l_myMacro____x40_Init_Notation___hyg_13781____closed__9;
lean_inc(x_13);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_push(x_16, x_20);
x_22 = lean_array_push(x_21, x_8);
x_23 = l_myMacro____x40_Init_Notation___hyg_13781____closed__8;
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = lean_array_push(x_16, x_24);
x_26 = l_Lean_nullKind___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_array_push(x_18, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_push(x_17, x_29);
x_31 = l_prec_x28___x29___closed__7;
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_13);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_push(x_30, x_32);
x_34 = l_myMacro____x40_Init_Notation___hyg_12262____closed__8;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_11, 0, x_35);
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = l_prec_x28___x29___closed__3;
lean_inc(x_36);
x_39 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Array_empty___closed__1;
x_41 = lean_array_push(x_40, x_39);
x_42 = lean_array_push(x_40, x_10);
x_43 = l_myMacro____x40_Init_Notation___hyg_13781____closed__9;
lean_inc(x_36);
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_array_push(x_40, x_44);
x_46 = lean_array_push(x_45, x_8);
x_47 = l_myMacro____x40_Init_Notation___hyg_13781____closed__8;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_40, x_48);
x_50 = l_Lean_nullKind___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_42, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_array_push(x_41, x_53);
x_55 = l_prec_x28___x29___closed__7;
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_36);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_push(x_54, x_56);
x_58 = l_myMacro____x40_Init_Notation___hyg_12262____closed__8;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_37);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_5);
lean_dec(x_1);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
return x_62;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_StructInst_expandStructInstExpectedType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_expandStructInstExpectedType___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_265____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("src");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_291; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
x_291 = lean_st_ref_take(x_7, x_8);
if (x_11 == 0)
{
lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = 0;
x_12 = x_294;
x_13 = x_292;
x_14 = x_293;
goto block_290;
}
else
{
lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_291, 1);
lean_inc(x_296);
lean_dec(x_291);
x_297 = 1;
x_12 = x_297;
x_13 = x_295;
x_14 = x_296;
goto block_290;
}
block_290:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_nat_add(x_16, x_9);
lean_ctor_set(x_13, 1, x_17);
x_18 = lean_st_ref_set(x_7, x_13, x_14);
if (x_12 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 4);
lean_dec(x_21);
lean_ctor_set(x_2, 4, x_16);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_isLocalIdent_x3f(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4;
x_37 = l_Lean_addMacroScope(x_34, x_36, x_31);
x_38 = lean_box(0);
x_39 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3;
x_40 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_40, 0, x_28);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
x_41 = l_Lean_Syntax_setArg(x_10, x_22, x_40);
x_42 = l_Lean_Syntax_setArg(x_1, x_9, x_41);
x_43 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_35);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_48);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_myMacro____x40_Init_Notation___hyg_14350____closed__1;
lean_inc(x_44);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_53);
x_56 = l_Lean_addMacroScope(x_51, x_36, x_47);
lean_inc(x_44);
x_57 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_38);
x_58 = lean_array_push(x_54, x_57);
x_59 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_60 = lean_array_push(x_58, x_59);
x_61 = lean_array_push(x_60, x_59);
x_62 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_44);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_push(x_61, x_63);
x_65 = lean_array_push(x_64, x_23);
x_66 = l_myMacro____x40_Init_Notation___hyg_14350____closed__6;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_array_push(x_54, x_67);
x_69 = l_myMacro____x40_Init_Notation___hyg_14350____closed__4;
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_array_push(x_55, x_70);
x_72 = l_myMacro____x40_Init_Notation___hyg_14350____closed__12;
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_44);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_push(x_54, x_73);
x_75 = l_Lean_nullKind___closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = lean_array_push(x_71, x_76);
x_78 = lean_array_push(x_77, x_42);
x_79 = l_myMacro____x40_Init_Notation___hyg_14350____closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_49, 0, x_81);
return x_49;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_82 = lean_ctor_get(x_49, 0);
x_83 = lean_ctor_get(x_49, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_49);
x_84 = l_myMacro____x40_Init_Notation___hyg_14350____closed__1;
lean_inc(x_44);
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_44);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Array_empty___closed__1;
x_87 = lean_array_push(x_86, x_85);
x_88 = l_Lean_addMacroScope(x_82, x_36, x_47);
lean_inc(x_44);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_44);
lean_ctor_set(x_89, 1, x_39);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_38);
x_90 = lean_array_push(x_86, x_89);
x_91 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_92 = lean_array_push(x_90, x_91);
x_93 = lean_array_push(x_92, x_91);
x_94 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_44);
x_95 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_95, 0, x_44);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_array_push(x_93, x_95);
x_97 = lean_array_push(x_96, x_23);
x_98 = l_myMacro____x40_Init_Notation___hyg_14350____closed__6;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_array_push(x_86, x_99);
x_101 = l_myMacro____x40_Init_Notation___hyg_14350____closed__4;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_87, x_102);
x_104 = l_myMacro____x40_Init_Notation___hyg_14350____closed__12;
x_105 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_105, 0, x_44);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_86, x_105);
x_107 = l_Lean_nullKind___closed__2;
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = lean_array_push(x_103, x_108);
x_110 = lean_array_push(x_109, x_42);
x_111 = l_myMacro____x40_Init_Notation___hyg_14350____closed__2;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_83);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_24);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_24, 0);
lean_dec(x_116);
x_117 = lean_box(0);
lean_ctor_set(x_24, 0, x_117);
return x_24;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_24, 1);
lean_inc(x_118);
lean_dec(x_24);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
x_124 = lean_ctor_get(x_2, 3);
x_125 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_126 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_127 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_128 = lean_ctor_get(x_2, 5);
lean_inc(x_128);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_2);
x_129 = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(x_129, 0, x_121);
lean_ctor_set(x_129, 1, x_122);
lean_ctor_set(x_129, 2, x_123);
lean_ctor_set(x_129, 3, x_124);
lean_ctor_set(x_129, 4, x_16);
lean_ctor_set(x_129, 5, x_128);
lean_ctor_set_uint8(x_129, sizeof(void*)*6, x_125);
lean_ctor_set_uint8(x_129, sizeof(void*)*6 + 1, x_126);
lean_ctor_set_uint8(x_129, sizeof(void*)*6 + 2, x_127);
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Syntax_getArg(x_10, x_130);
lean_inc(x_4);
lean_inc(x_131);
x_132 = l_Lean_Elab_Term_isLocalIdent_x3f(x_131, x_129, x_3, x_4, x_5, x_6, x_7, x_19);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Elab_Term_getCurrMacroScope(x_129, x_3, x_4, x_5, x_6, x_7, x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4;
x_145 = l_Lean_addMacroScope(x_142, x_144, x_139);
x_146 = lean_box(0);
x_147 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3;
x_148 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_148, 0, x_136);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_145);
lean_ctor_set(x_148, 3, x_146);
x_149 = l_Lean_Syntax_setArg(x_10, x_130, x_148);
x_150 = l_Lean_Syntax_setArg(x_1, x_9, x_149);
x_151 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_143);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_Elab_Term_getCurrMacroScope(x_129, x_3, x_4, x_5, x_6, x_7, x_153);
lean_dec(x_4);
lean_dec(x_129);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = l_myMacro____x40_Init_Notation___hyg_14350____closed__1;
lean_inc(x_152);
x_162 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_162, 0, x_152);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Array_empty___closed__1;
x_164 = lean_array_push(x_163, x_162);
x_165 = l_Lean_addMacroScope(x_158, x_144, x_155);
lean_inc(x_152);
x_166 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_166, 0, x_152);
lean_ctor_set(x_166, 1, x_147);
lean_ctor_set(x_166, 2, x_165);
lean_ctor_set(x_166, 3, x_146);
x_167 = lean_array_push(x_163, x_166);
x_168 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_169 = lean_array_push(x_167, x_168);
x_170 = lean_array_push(x_169, x_168);
x_171 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_152);
x_172 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_172, 0, x_152);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_push(x_170, x_172);
x_174 = lean_array_push(x_173, x_131);
x_175 = l_myMacro____x40_Init_Notation___hyg_14350____closed__6;
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_174);
x_177 = lean_array_push(x_163, x_176);
x_178 = l_myMacro____x40_Init_Notation___hyg_14350____closed__4;
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
x_180 = lean_array_push(x_164, x_179);
x_181 = l_myMacro____x40_Init_Notation___hyg_14350____closed__12;
x_182 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_182, 0, x_152);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_array_push(x_163, x_182);
x_184 = l_Lean_nullKind___closed__2;
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_push(x_180, x_185);
x_187 = lean_array_push(x_186, x_150);
x_188 = l_myMacro____x40_Init_Notation___hyg_14350____closed__2;
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
if (lean_is_scalar(x_160)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_160;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_159);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_192 = lean_ctor_get(x_132, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_193 = x_132;
} else {
 lean_dec_ref(x_132);
 x_193 = lean_box(0);
}
x_194 = lean_box(0);
if (lean_is_scalar(x_193)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_193;
}
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_192);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_18);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_18, 0);
lean_dec(x_197);
x_198 = lean_box(0);
lean_ctor_set(x_18, 0, x_198);
return x_18;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_18, 1);
lean_inc(x_199);
lean_dec(x_18);
x_200 = lean_box(0);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_202 = lean_ctor_get(x_13, 0);
x_203 = lean_ctor_get(x_13, 1);
x_204 = lean_ctor_get(x_13, 2);
x_205 = lean_ctor_get(x_13, 3);
lean_inc(x_205);
lean_inc(x_204);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_13);
x_206 = lean_nat_add(x_203, x_9);
x_207 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_204);
lean_ctor_set(x_207, 3, x_205);
x_208 = lean_st_ref_set(x_7, x_207, x_14);
if (x_12 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_210 = lean_ctor_get(x_2, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_2, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_2, 3);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_215 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 1);
x_216 = lean_ctor_get_uint8(x_2, sizeof(void*)*6 + 2);
x_217 = lean_ctor_get(x_2, 5);
lean_inc(x_217);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 x_218 = x_2;
} else {
 lean_dec_ref(x_2);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 6, 3);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_210);
lean_ctor_set(x_219, 1, x_211);
lean_ctor_set(x_219, 2, x_212);
lean_ctor_set(x_219, 3, x_213);
lean_ctor_set(x_219, 4, x_203);
lean_ctor_set(x_219, 5, x_217);
lean_ctor_set_uint8(x_219, sizeof(void*)*6, x_214);
lean_ctor_set_uint8(x_219, sizeof(void*)*6 + 1, x_215);
lean_ctor_set_uint8(x_219, sizeof(void*)*6 + 2, x_216);
x_220 = lean_unsigned_to_nat(0u);
x_221 = l_Lean_Syntax_getArg(x_10, x_220);
lean_inc(x_4);
lean_inc(x_221);
x_222 = l_Lean_Elab_Term_isLocalIdent_x3f(x_221, x_219, x_3, x_4, x_5, x_6, x_7, x_209);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_6, x_7, x_224);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lean_Elab_Term_getCurrMacroScope(x_219, x_3, x_4, x_5, x_6, x_7, x_227);
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_230);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4;
x_235 = l_Lean_addMacroScope(x_232, x_234, x_229);
x_236 = lean_box(0);
x_237 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3;
x_238 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_238, 0, x_226);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_235);
lean_ctor_set(x_238, 3, x_236);
x_239 = l_Lean_Syntax_setArg(x_10, x_220, x_238);
x_240 = l_Lean_Syntax_setArg(x_1, x_9, x_239);
x_241 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__4___rarg(x_6, x_7, x_233);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Elab_Term_getCurrMacroScope(x_219, x_3, x_4, x_5, x_6, x_7, x_243);
lean_dec(x_4);
lean_dec(x_219);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_246);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
x_251 = l_myMacro____x40_Init_Notation___hyg_14350____closed__1;
lean_inc(x_242);
x_252 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_252, 0, x_242);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Array_empty___closed__1;
x_254 = lean_array_push(x_253, x_252);
x_255 = l_Lean_addMacroScope(x_248, x_234, x_245);
lean_inc(x_242);
x_256 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_256, 0, x_242);
lean_ctor_set(x_256, 1, x_237);
lean_ctor_set(x_256, 2, x_255);
lean_ctor_set(x_256, 3, x_236);
x_257 = lean_array_push(x_253, x_256);
x_258 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_259 = lean_array_push(x_257, x_258);
x_260 = lean_array_push(x_259, x_258);
x_261 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_242);
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_242);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_array_push(x_260, x_262);
x_264 = lean_array_push(x_263, x_221);
x_265 = l_myMacro____x40_Init_Notation___hyg_14350____closed__6;
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
x_267 = lean_array_push(x_253, x_266);
x_268 = l_myMacro____x40_Init_Notation___hyg_14350____closed__4;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_array_push(x_254, x_269);
x_271 = l_myMacro____x40_Init_Notation___hyg_14350____closed__12;
x_272 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_272, 0, x_242);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_array_push(x_253, x_272);
x_274 = l_Lean_nullKind___closed__2;
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
x_276 = lean_array_push(x_270, x_275);
x_277 = lean_array_push(x_276, x_240);
x_278 = l_myMacro____x40_Init_Notation___hyg_14350____closed__2;
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
if (lean_is_scalar(x_250)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_250;
}
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_249);
return x_281;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_219);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_282 = lean_ctor_get(x_222, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_283 = x_222;
} else {
 lean_dec_ref(x_222);
 x_283 = lean_box(0);
}
x_284 = lean_box(0);
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_284);
lean_ctor_set(x_285, 1, x_282);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_203);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_ctor_get(x_208, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_287 = x_208;
} else {
 lean_dec_ref(x_208);
 x_287 = lean_box(0);
}
x_288 = lean_box(0);
if (lean_is_scalar(x_287)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_287;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_286);
return x_289;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
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
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Source_isNone_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Source_isNone(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_setStructSourceSyntax_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_mkOptionalNode___closed__1;
x_5 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_setArg(x_5, x_6, x_4);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_mkOptionalNode___closed__1;
x_11 = l_Lean_Syntax_setArg(x_1, x_9, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Syntax_setArg(x_11, x_12, x_8);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_setArg(x_1, x_15, x_14);
x_17 = lean_unsigned_to_nat(3u);
x_18 = l_Lean_mkOptionalNode___closed__1;
x_19 = l_Lean_Syntax_setArg(x_16, x_17, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid structure instance `with` and `..` cannot be used together");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.StructInst");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.getStructSource");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5;
x_3 = lean_unsigned_to_nat(81u);
x_4 = lean_unsigned_to_nat(21u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_15 = lean_ctor_get(x_6, 3);
x_16 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
lean_ctor_set(x_6, 3, x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_dec(x_12);
x_19 = l_Lean_Syntax_isNone(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3;
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Syntax_getArg(x_10, x_17);
lean_inc(x_4);
x_23 = l_Lean_Elab_Term_isLocalIdent_x3f(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_10);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = lean_apply_7(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_25);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_23, 0, x_33);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_ctor_get(x_24, 0);
lean_inc(x_35);
lean_dec(x_24);
x_36 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_36, 0, x_10);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_38 = lean_ctor_get(x_6, 0);
x_39 = lean_ctor_get(x_6, 1);
x_40 = lean_ctor_get(x_6, 2);
x_41 = lean_ctor_get(x_6, 3);
x_42 = lean_ctor_get(x_6, 4);
x_43 = lean_ctor_get(x_6, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_6);
x_44 = l_Lean_replaceRef(x_1, x_41);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Syntax_getArg(x_12, x_46);
lean_dec(x_12);
x_48 = l_Lean_Syntax_isNone(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_10);
x_49 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3;
x_50 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1(x_49, x_2, x_3, x_4, x_5, x_45, x_7, x_8);
lean_dec(x_7);
lean_dec(x_45);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = l_Lean_Syntax_getArg(x_10, x_46);
lean_inc(x_4);
x_52 = l_Lean_Elab_Term_isLocalIdent_x3f(x_51, x_2, x_3, x_4, x_5, x_45, x_7, x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_56 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6;
x_57 = lean_panic_fn(x_55, x_56);
x_58 = lean_apply_7(x_57, x_2, x_3, x_4, x_5, x_45, x_7, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_45);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_60 = x_52;
} else {
 lean_dec_ref(x_52);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_53, 0);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Syntax_getArg(x_12, x_64);
x_66 = l_Lean_Syntax_isNone(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_12);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_12);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
return x_70;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, can't mix field and `[..]` at a given level");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, at most one `[..]` at a given level");
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_2 == x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_getArg(x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_Syntax_getArg(x_15, x_14);
x_17 = l_Lean_Syntax_getArg(x_16, x_14);
lean_dec(x_16);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = 1;
x_23 = x_2 + x_22;
x_2 = x_23;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = l_Lean_Syntax_getKind(x_25);
x_27 = lean_name_eq(x_26, x_19);
lean_dec(x_26);
if (x_27 == 0)
{
size_t x_28; size_t x_29; 
lean_dec(x_15);
x_28 = 1;
x_29 = x_2 + x_28;
x_2 = x_29;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_4);
x_31 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_32 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_15, x_31, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_37; size_t x_38; size_t x_39; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_15);
x_38 = 1;
x_39 = x_2 + x_38;
x_2 = x_39;
x_4 = x_37;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_4, 0);
lean_inc(x_41);
lean_dec(x_4);
x_42 = l_Lean_Syntax_getKind(x_41);
x_43 = lean_name_eq(x_42, x_19);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__3;
x_45 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_15, x_44, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___closed__6;
x_51 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_15, x_50, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; 
lean_dec(x_9);
lean_dec(x_5);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_11);
return x_56;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_box(0);
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_1, x_23);
x_25 = l_Lean_Syntax_getArgs(x_24);
lean_dec(x_24);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_6);
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
lean_dec(x_6);
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
x_18 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isModifyOp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("struct");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_1080____closed__1;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modifyOp");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_MacroExpansionInfo_format___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nval: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nSource: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_314; lean_object* x_315; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_328 = lean_st_ref_get(x_10, x_11);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_329, 3);
lean_inc(x_330);
lean_dec(x_329);
x_331 = lean_ctor_get_uint8(x_330, sizeof(void*)*1);
lean_dec(x_330);
if (x_331 == 0)
{
lean_object* x_332; uint8_t x_333; 
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
lean_dec(x_328);
x_333 = 0;
x_314 = x_333;
x_315 = x_332;
goto block_327;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_334 = lean_ctor_get(x_328, 1);
lean_inc(x_334);
lean_dec(x_328);
x_335 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_336 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_335, x_5, x_6, x_7, x_8, x_9, x_10, x_334);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_unbox(x_337);
lean_dec(x_337);
x_314 = x_339;
x_315 = x_338;
goto block_327;
}
block_313:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_14, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_18 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8;
x_28 = l_Lean_addMacroScope(x_25, x_27, x_22);
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7;
x_31 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_29);
x_32 = l_Lean_Syntax_getArg(x_16, x_13);
lean_inc(x_32);
x_33 = l_Lean_Syntax_getKind(x_32);
x_34 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_toSubarray___rarg(x_36, x_15, x_37);
x_39 = l_Array_ofSubarray___rarg(x_38);
lean_dec(x_38);
x_40 = l_Lean_nullKind;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_st_ref_get(x_10, x_26);
if (x_35 == 0)
{
lean_object* x_203; 
x_203 = l_Lean_Syntax_getArg(x_32, x_15);
lean_dec(x_32);
x_43 = x_203;
goto block_202;
}
else
{
x_43 = x_32;
goto block_202;
}
block_202:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_44 = l_Lean_Syntax_mkApp___closed__1;
x_45 = lean_array_push(x_44, x_43);
x_46 = lean_array_push(x_45, x_41);
x_47 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_265____closed__6;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Syntax_setArg(x_2, x_13, x_48);
x_50 = lean_array_push(x_44, x_49);
x_51 = l_Lean_mkOptionalNode___closed__1;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_mkOptionalNode___closed__2;
x_55 = lean_array_push(x_54, x_53);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_55);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_193 = lean_ctor_get(x_3, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_3, 1);
lean_inc(x_194);
x_195 = lean_array_get_size(x_194);
x_196 = lean_nat_dec_lt(x_13, x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_31);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_193);
lean_ctor_set(x_197, 1, x_194);
x_57 = x_197;
goto block_192;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_box(0);
x_199 = lean_array_fset(x_194, x_13, x_198);
x_200 = lean_array_fset(x_199, x_13, x_31);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_200);
x_57 = x_201;
goto block_192;
}
}
else
{
lean_dec(x_31);
lean_inc(x_3);
x_57 = x_3;
goto block_192;
}
block_192:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_167; lean_object* x_168; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
lean_inc(x_1);
x_58 = l_Lean_Syntax_setArg(x_1, x_15, x_57);
x_59 = lean_unsigned_to_nat(2u);
x_60 = l_Lean_Syntax_setArg(x_58, x_59, x_56);
x_181 = lean_ctor_get(x_42, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_181, 3);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_ctor_get_uint8(x_182, sizeof(void*)*1);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_42, 1);
lean_inc(x_184);
lean_dec(x_42);
x_185 = 0;
x_167 = x_185;
x_168 = x_184;
goto block_180;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_186 = lean_ctor_get(x_42, 1);
lean_inc(x_186);
lean_dec(x_42);
x_187 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_188 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_187, x_5, x_6, x_7, x_8, x_9, x_10, x_186);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_unbox(x_189);
lean_dec(x_189);
x_167 = x_191;
x_168 = x_190;
goto block_180;
}
block_166:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_62 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
x_63 = l_Lean_Syntax_getArg(x_62, x_15);
lean_dec(x_62);
x_64 = l_Lean_Syntax_getArg(x_3, x_13);
lean_dec(x_3);
x_65 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_64);
x_76 = l_Lean_Name_toString___closed__1;
lean_inc(x_66);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_75, x_77);
x_79 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11;
lean_inc(x_69);
lean_inc(x_72);
x_80 = l_Lean_addMacroScope(x_72, x_79, x_69);
x_81 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10;
lean_inc(x_66);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_66);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_29);
x_83 = lean_array_push(x_78, x_82);
x_84 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = lean_array_push(x_74, x_85);
x_87 = l_prec_x28___x29___closed__3;
lean_inc(x_66);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_66);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_push(x_74, x_88);
x_90 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_inc(x_69);
lean_inc(x_72);
x_91 = l_Lean_addMacroScope(x_72, x_90, x_69);
x_92 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13;
lean_inc(x_66);
x_93 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_93, 0, x_66);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_91);
lean_ctor_set(x_93, 3, x_29);
lean_inc(x_89);
x_94 = lean_array_push(x_89, x_93);
x_95 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_66);
x_96 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_96, 0, x_66);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_94, x_96);
x_98 = lean_array_push(x_97, x_63);
x_99 = l_prec_x28___x29___closed__7;
lean_inc(x_66);
x_100 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_100, 0, x_66);
lean_ctor_set(x_100, 1, x_99);
lean_inc(x_100);
x_101 = lean_array_push(x_98, x_100);
x_102 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_array_push(x_74, x_103);
x_105 = l_myMacro____x40_Init_Notation___hyg_12262____closed__9;
lean_inc(x_66);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_66);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_array_push(x_74, x_106);
x_108 = l_Lean_addMacroScope(x_72, x_27, x_69);
lean_inc(x_66);
x_109 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_109, 0, x_66);
lean_ctor_set(x_109, 1, x_30);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_29);
x_110 = lean_array_push(x_74, x_109);
x_111 = l_Lean_nullKind___closed__2;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
x_113 = lean_array_push(x_74, x_112);
x_114 = l_myMacro____x40_Init_Notation___hyg_12262____closed__13;
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_66);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_push(x_113, x_115);
x_117 = lean_array_push(x_116, x_60);
x_118 = l_myMacro____x40_Init_Notation___hyg_12262____closed__12;
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
x_120 = lean_array_push(x_107, x_119);
x_121 = l_myMacro____x40_Init_Notation___hyg_12262____closed__10;
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
x_123 = lean_array_push(x_74, x_122);
x_124 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_125 = lean_array_push(x_123, x_124);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_111);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_array_push(x_89, x_126);
x_128 = lean_array_push(x_127, x_100);
x_129 = l_myMacro____x40_Init_Notation___hyg_12262____closed__8;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_array_push(x_104, x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_111);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_array_push(x_86, x_132);
x_134 = l_myMacro____x40_Init_Notation___hyg_2117____closed__4;
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_154 = lean_st_ref_get(x_10, x_73);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_155, 3);
lean_inc(x_156);
lean_dec(x_155);
x_157 = lean_ctor_get_uint8(x_156, sizeof(void*)*1);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_154, 1);
lean_inc(x_158);
lean_dec(x_154);
x_159 = 0;
x_136 = x_159;
x_137 = x_158;
goto block_153;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_161 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_162 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_161, x_5, x_6, x_7, x_8, x_9, x_10, x_160);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_unbox(x_163);
lean_dec(x_163);
x_136 = x_165;
x_137 = x_164;
goto block_153;
}
block_153:
{
if (x_136 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_inc(x_135);
lean_inc(x_1);
x_138 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_138, 0, x_1);
lean_closure_set(x_138, 1, x_135);
lean_closure_set(x_138, 2, x_4);
x_139 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_1, x_135, x_138, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_1);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_1);
x_141 = l_Lean_KernelException_toMessageData___closed__15;
x_142 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
lean_inc(x_135);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_135);
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_141);
x_148 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_149 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_148, x_147, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
lean_inc(x_135);
lean_inc(x_1);
x_151 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_151, 0, x_1);
lean_closure_set(x_151, 1, x_135);
lean_closure_set(x_151, 2, x_4);
x_152 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_1, x_135, x_151, x_5, x_6, x_7, x_8, x_9, x_10, x_150);
return x_152;
}
}
}
block_180:
{
if (x_167 == 0)
{
x_61 = x_168;
goto block_166;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_inc(x_1);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_1);
x_170 = l_Lean_KernelException_toMessageData___closed__15;
x_171 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16;
x_173 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_60);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_60);
x_175 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_170);
x_177 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_178 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_177, x_176, x_5, x_6, x_7, x_8, x_9, x_10, x_168);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_61 = x_179;
goto block_166;
}
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
lean_dec(x_16);
x_204 = lean_unsigned_to_nat(2u);
x_205 = l_Lean_Syntax_getArg(x_2, x_204);
lean_dec(x_2);
x_206 = l_Lean_Syntax_getArg(x_14, x_13);
lean_dec(x_14);
x_207 = l_Lean_Syntax_getArg(x_206, x_15);
lean_dec(x_206);
x_208 = l_Lean_Syntax_getArg(x_3, x_13);
lean_dec(x_3);
x_209 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_Elab_Term_quoteAutoTactic___spec__1___rarg(x_9, x_10, x_12);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
x_215 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_214);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Array_empty___closed__1;
x_219 = lean_array_push(x_218, x_208);
x_220 = l_Lean_Name_toString___closed__1;
lean_inc(x_210);
x_221 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_221, 0, x_210);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_array_push(x_219, x_221);
x_223 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11;
lean_inc(x_213);
lean_inc(x_216);
x_224 = l_Lean_addMacroScope(x_216, x_223, x_213);
x_225 = lean_box(0);
x_226 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10;
lean_inc(x_210);
x_227 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_227, 0, x_210);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_224);
lean_ctor_set(x_227, 3, x_225);
x_228 = lean_array_push(x_222, x_227);
x_229 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_array_push(x_218, x_230);
x_232 = l_prec_x28___x29___closed__3;
lean_inc(x_210);
x_233 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_233, 0, x_210);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_array_push(x_218, x_233);
x_235 = l___private_Lean_Elab_App_0__Lean_Elab_Term_elabAppLValsAux_loop___closed__2;
lean_inc(x_213);
lean_inc(x_216);
x_236 = l_Lean_addMacroScope(x_216, x_235, x_213);
x_237 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13;
lean_inc(x_210);
x_238 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_238, 0, x_210);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_238, 2, x_236);
lean_ctor_set(x_238, 3, x_225);
lean_inc(x_234);
x_239 = lean_array_push(x_234, x_238);
x_240 = l_myMacro____x40_Init_Notation___hyg_14350____closed__11;
lean_inc(x_210);
x_241 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_241, 0, x_210);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_push(x_239, x_241);
x_243 = lean_array_push(x_242, x_207);
x_244 = l_prec_x28___x29___closed__7;
lean_inc(x_210);
x_245 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_245, 0, x_210);
lean_ctor_set(x_245, 1, x_244);
lean_inc(x_245);
x_246 = lean_array_push(x_243, x_245);
x_247 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = lean_array_push(x_218, x_248);
x_250 = l_myMacro____x40_Init_Notation___hyg_12262____closed__9;
lean_inc(x_210);
x_251 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_251, 0, x_210);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_array_push(x_218, x_251);
x_253 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8;
x_254 = l_Lean_addMacroScope(x_216, x_253, x_213);
x_255 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7;
lean_inc(x_210);
x_256 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_256, 0, x_210);
lean_ctor_set(x_256, 1, x_255);
lean_ctor_set(x_256, 2, x_254);
lean_ctor_set(x_256, 3, x_225);
x_257 = lean_array_push(x_218, x_256);
x_258 = l_Lean_nullKind___closed__2;
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_array_push(x_218, x_259);
x_261 = l_myMacro____x40_Init_Notation___hyg_12262____closed__13;
x_262 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_262, 0, x_210);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_array_push(x_260, x_262);
x_264 = lean_array_push(x_263, x_205);
x_265 = l_myMacro____x40_Init_Notation___hyg_12262____closed__12;
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
x_267 = lean_array_push(x_252, x_266);
x_268 = l_myMacro____x40_Init_Notation___hyg_12262____closed__10;
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_267);
x_270 = lean_array_push(x_218, x_269);
x_271 = l_myMacro____x40_Init_Notation___hyg_1324____closed__8;
x_272 = lean_array_push(x_270, x_271);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_258);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_array_push(x_234, x_273);
x_275 = lean_array_push(x_274, x_245);
x_276 = l_myMacro____x40_Init_Notation___hyg_12262____closed__8;
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = lean_array_push(x_249, x_277);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_258);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_array_push(x_231, x_279);
x_281 = l_myMacro____x40_Init_Notation___hyg_2117____closed__4;
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_301 = lean_st_ref_get(x_10, x_217);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_302, 3);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_ctor_get_uint8(x_303, sizeof(void*)*1);
lean_dec(x_303);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
x_306 = 0;
x_283 = x_306;
x_284 = x_305;
goto block_300;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_307 = lean_ctor_get(x_301, 1);
lean_inc(x_307);
lean_dec(x_301);
x_308 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_309 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_308, x_5, x_6, x_7, x_8, x_9, x_10, x_307);
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_309, 1);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_unbox(x_310);
lean_dec(x_310);
x_283 = x_312;
x_284 = x_311;
goto block_300;
}
block_300:
{
if (x_283 == 0)
{
lean_object* x_285; lean_object* x_286; 
lean_inc(x_282);
lean_inc(x_1);
x_285 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_285, 0, x_1);
lean_closure_set(x_285, 1, x_282);
lean_closure_set(x_285, 2, x_4);
x_286 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_1, x_282, x_285, x_5, x_6, x_7, x_8, x_9, x_10, x_284);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_inc(x_1);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_1);
x_288 = l_Lean_KernelException_toMessageData___closed__15;
x_289 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_287);
x_290 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14;
x_291 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
lean_inc(x_282);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_282);
x_293 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_288);
x_295 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_296 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_295, x_294, x_5, x_6, x_7, x_8, x_9, x_10, x_284);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
lean_inc(x_282);
lean_inc(x_1);
x_298 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_298, 0, x_1);
lean_closure_set(x_298, 1, x_282);
lean_closure_set(x_298, 2, x_4);
x_299 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_1, x_282, x_298, x_5, x_6, x_7, x_8, x_9, x_10, x_297);
return x_299;
}
}
}
}
block_327:
{
if (x_314 == 0)
{
x_12 = x_315;
goto block_313;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_inc(x_2);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_2);
x_317 = l_Lean_KernelException_toMessageData___closed__15;
x_318 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
x_319 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18;
x_320 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
lean_inc(x_3);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_3);
x_322 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_317);
x_324 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4;
x_325 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_324, x_323, x_5, x_6, x_7, x_8, x_9, x_10, x_315);
x_326 = lean_ctor_get(x_325, 1);
lean_inc(x_326);
lean_dec(x_325);
x_12 = x_326;
goto block_313;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_3, x_6, x_7, x_2);
return x_8;
}
else
{
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_apply_1(x_5, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_2(x_4, x_1, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__2___rarg), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_match__4___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, expected type is not known");
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___closed__2;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_mk_string("invalid {...} notation, ");
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
x_1 = lean_mk_string(" type is not of the form (C ...)");
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_instantiateMVars(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
x_22 = l_Lean_KernelException_toMessageData___closed__15;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_mkAuxName___spec__1(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; 
lean_dec(x_11);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("source");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected");
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_inferType(x_12, x_5, x_6, x_7, x_8, x_11);
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
x_16 = l_Lean_Meta_whnf(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_tryPostponeIfMVar(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = l_Lean_Expr_getAppFn(x_17);
if (lean_obj_tag(x_23) == 4)
{
lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_free_object(x_19);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
x_26 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_17, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_Expr_getAppFn(x_17);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
x_32 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_17, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
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
lean_dec(x_2);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_dec(x_10);
x_46 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnknownExpectedType(x_3, x_4, x_5, x_6, x_7, x_8, x_45);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_10, 1);
lean_inc(x_47);
lean_dec(x_10);
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_48);
x_49 = l_Lean_Meta_whnf(x_48, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
x_53 = l_Lean_Expr_getAppFn(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
lean_ctor_set(x_49, 0, x_54);
return x_49;
}
else
{
lean_dec(x_53);
lean_free_object(x_49);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_inferType(x_55, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_whnf(x_57, x_5, x_6, x_7, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_62 = l_Lean_Elab_Term_tryPostponeIfMVar(x_60, x_3, x_4, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 1);
x_65 = lean_ctor_get(x_62, 0);
lean_dec(x_65);
x_66 = l_Lean_Expr_getAppFn(x_60);
if (lean_obj_tag(x_66) == 4)
{
lean_object* x_67; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
lean_ctor_set(x_62, 0, x_67);
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
lean_free_object(x_62);
x_68 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
x_69 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_60, x_68, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = l_Lean_Expr_getAppFn(x_60);
if (lean_obj_tag(x_71) == 4)
{
lean_object* x_72; lean_object* x_73; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_71);
x_74 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
x_75 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_60, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_70);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_62);
if (x_76 == 0)
{
return x_62;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_62, 0);
x_78 = lean_ctor_get(x_62, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_62);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_80 = !lean_is_exclusive(x_59);
if (x_80 == 0)
{
return x_59;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_59, 0);
x_82 = lean_ctor_get(x_59, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_59);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_84 = !lean_is_exclusive(x_56);
if (x_84 == 0)
{
return x_56;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_56, 0);
x_86 = lean_ctor_get(x_56, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_56);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_88 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2;
x_89 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_48, x_88, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_49, 0);
x_91 = lean_ctor_get(x_49, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_49);
x_92 = l_Lean_Expr_getAppFn(x_90);
lean_dec(x_90);
if (lean_obj_tag(x_92) == 4)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_dec(x_92);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_48);
x_95 = lean_ctor_get(x_2, 1);
lean_inc(x_95);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_Meta_inferType(x_95, x_5, x_6, x_7, x_8, x_91);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_99 = l_Lean_Meta_whnf(x_97, x_5, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_100);
x_102 = l_Lean_Elab_Term_tryPostponeIfMVar(x_100, x_3, x_4, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Expr_getAppFn(x_100);
if (lean_obj_tag(x_105) == 4)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_100);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_105);
lean_dec(x_104);
x_108 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1;
x_109 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_100, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_103);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_100);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_112 = x_102;
} else {
 lean_dec_ref(x_102);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_114 = lean_ctor_get(x_99, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_99, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_116 = x_99;
} else {
 lean_dec_ref(x_99);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_118 = lean_ctor_get(x_96, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_96, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_120 = x_96;
} else {
 lean_dec_ref(x_96);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_2);
x_122 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2;
x_123 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName_throwUnexpectedExpectedType(x_48, x_122, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_49);
if (x_124 == 0)
{
return x_49;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_49, 0);
x_126 = lean_ctor_get(x_49, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_49);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_10);
if (x_128 == 0)
{
return x_10;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_10, 0);
x_130 = lean_ctor_get(x_10, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_10);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_4, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_instToFormatFieldLHS_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_instToFormatFieldLHS(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_prettyPrint(x_6);
x_8 = l_Std_Format_sbracket___closed__3;
x_9 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Std_Format_sbracket___closed__4;
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
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
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedFieldVal(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Term_StructInst_instInhabitedField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedField___closed__1;
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_apply_4(x_2, x_10, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_apply_1(x_3, x_1);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_isSimple_match__1___rarg), 3, 0);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object* x_1) {
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_4);
return x_5;
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
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_allDefault_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_allDefault_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_allDefault_match__3___rarg), 2, 0);
return x_2;
}
}
uint8_t l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_1, x_4);
x_6 = lean_ctor_get(x_3, 2);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
case 1:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 0);
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
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 1;
x_4 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___at_Lean_Elab_Term_StructInst_Struct_allDefault___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_ref_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_structName_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_fields_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_source_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatField_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatField_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatField_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = l_Std_Format_sbracket___closed__3;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Std_Format_sbracket___closed__4;
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_2);
x_17 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_4, x_2);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_fmt___at_Lean_Level_PP_Result_format___spec__1(x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
case 1:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
default: 
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_Syntax_prettyPrint(x_26);
x_28 = l_Std_Format_sbracket___closed__3;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Std_Format_sbracket___closed__4;
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_17);
return x_33;
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
x_1 = lean_mk_string(" . ");
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
x_1 = lean_mk_string("<default>");
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
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Elab_Term_StructInst_formatField___closed__2;
x_5 = l_Std_Format_joinSep___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_3, x_4);
x_6 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_5935____closed__4;
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
x_15 = l_Lean_Elab_Term_StructInst_formatField___closed__4;
x_16 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct_match__2___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct), 1, 0);
return x_1;
}
}
lean_object* l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(lean_object* x_1) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_7 = l_Lean_Elab_Term_StructInst_formatField(x_6, x_4);
x_8 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(x_5);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
x_12 = l_Lean_Elab_Term_StructInst_formatField(x_11, x_9);
x_13 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" .. }");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Tactic_changeWith___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1(x_2);
x_5 = l_instReprSigma___rarg___closed__1;
x_6 = l_Std_Format_joinSep___at_instReprProd___spec__1(x_4, x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Json_render___closed__7;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Json_render___closed__8;
x_10 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
x_11 = l_Lean_Json_render___closed__7;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
x_13 = l_Lean_Elab_Term_StructInst_formatStruct___closed__2;
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
default: 
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Json_render___closed__7;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_Elab_Term_StructInst_formatStruct___closed__3;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_6);
x_23 = l_Lean_Json_render___closed__8;
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatStruct() {
_start:
{
lean_object* x_1; 
x_1 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Syntax_instToStringSyntax___closed__1;
x_2 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
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
x_1 = l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_instToFormatFieldStruct___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1;
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
x_1 = l_Lean_Syntax_instToStringSyntax___closed__1;
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
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_2(x_4, x_8, x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_2(x_2, x_11, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_mkAtomFrom(x_3, x_5);
x_7 = l_Lean_mkIdentFrom(x_3, x_4);
lean_dec(x_3);
x_8 = l_Lean_Syntax_mkApp___closed__1;
x_9 = lean_array_push(x_8, x_6);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_nullKind;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_mkIdentFrom(x_13, x_14);
lean_dec(x_13);
return x_15;
}
}
case 1:
{
if (x_1 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lean_Name_toString___closed__1;
x_18 = l_Lean_mkAtomFrom(x_16, x_17);
x_19 = l_Lean_Syntax_mkApp___closed__1;
x_20 = lean_array_push(x_19, x_18);
x_21 = lean_array_push(x_20, x_16);
x_22 = l_Lean_nullKind;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
return x_24;
}
}
default: 
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
return x_25;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_FieldVal_toSyntax_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.StructInst.FieldVal.toSyntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__1;
x_3 = lean_unsigned_to_nat(271u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object* x_1) {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedSyntax;
x_4 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Field_toSyntax_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 0;
x_11 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_10, x_9);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.StructInst.Field.toSyntax");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__1;
x_3 = lean_unsigned_to_nat(279u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
lean_dec(x_1);
x_3 = l_Lean_instInhabitedSyntax;
x_4 = l_Lean_Elab_Term_StructInst_Field_toSyntax___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l_Lean_Syntax_setArg(x_8, x_11, x_10);
x_13 = 1;
x_14 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_13, x_6);
x_15 = l_List_redLength___rarg(x_7);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_List_toArrayAux___rarg(x_7, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = x_17;
x_22 = l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_19, x_20, x_21);
x_23 = x_22;
x_24 = l_Lean_nullKind;
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Syntax_mkApp___closed__1;
x_27 = lean_array_push(x_26, x_14);
x_28 = lean_array_push(x_27, x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Lean_Syntax_setArg(x_12, x_30, x_29);
return x_31;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure syntax");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
lean_inc(x_1);
x_2 = l_Lean_Syntax_getKind(x_1);
x_3 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_4 = lean_name_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_nullKind;
x_6 = lean_name_eq(x_2, x_5);
lean_dec(x_2);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Syntax_isIdent(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_fieldIdxKind;
x_9 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = lean_erase_macro_scopes(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = l_Lean_Syntax_getArg(x_1, x_18);
lean_dec(x_1);
x_20 = l_Lean_Syntax_isIdent(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_fieldIdxKind;
x_22 = l___private_Init_Meta_0__Lean_Syntax_isNatLitAux(x_21, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec(x_19);
x_23 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2;
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Syntax_getId(x_19);
x_28 = lean_erase_macro_scopes(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_2);
x_31 = lean_unsigned_to_nat(1u);
x_32 = l_Lean_Syntax_getArg(x_1, x_31);
x_33 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_Syntax_getArg(x_9, x_7);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
lean_free_object(x_1);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
lean_free_object(x_1);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_10);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(0, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
if (lean_is_scalar(x_28)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_28;
}
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(2u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_4, x_8);
x_10 = l_Lean_Syntax_getArg(x_9, x_8);
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = l_Lean_Syntax_getArg(x_9, x_16);
lean_dec(x_9);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_array_to_list(lean_box(0), x_18);
x_20 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_24);
lean_ctor_set(x_1, 0, x_15);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_7);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__3(x_5);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(2u);
x_41 = l_Lean_Syntax_getArg(x_38, x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Lean_Syntax_getArg(x_38, x_42);
x_44 = l_Lean_Syntax_getArg(x_43, x_42);
x_45 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = lean_unsigned_to_nat(1u);
x_51 = l_Lean_Syntax_getArg(x_43, x_50);
lean_dec(x_43);
x_52 = l_Lean_Syntax_getArgs(x_51);
lean_dec(x_51);
x_53 = lean_array_to_list(lean_box(0), x_52);
x_54 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2(x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_49);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_41);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_38);
lean_ctor_set(x_62, 1, x_59);
lean_ctor_set(x_62, 2, x_60);
lean_ctor_set(x_62, 3, x_61);
x_63 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__3(x_39);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_65 = x_63;
} else {
 lean_dec_ref(x_63);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(0, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_67);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_9 = 0;
x_10 = x_6;
x_11 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_8, x_9, x_10);
x_12 = x_11;
x_13 = lean_array_to_list(lean_box(0), x_12);
x_14 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__3(x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_3);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1), 5, 4);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_4);
lean_closure_set(x_10, 2, x_5);
lean_closure_set(x_10, 3, x_7);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_apply_1(x_2, x_4);
lean_ctor_set(x_1, 2, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_10 = lean_apply_1(x_2, x_8);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_9);
return x_11;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Monad_seqRight___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_apply_1(x_4, x_1);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_usize(x_8, 2);
lean_dec(x_8);
x_17 = lean_box_usize(x_16);
x_18 = lean_apply_7(x_2, x_14, x_15, x_17, x_13, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_usize(x_8, 2);
x_26 = lean_box_usize(x_25);
x_27 = lean_apply_9(x_3, x_23, x_8, x_9, x_24, x_26, x_22, x_19, x_20, x_21);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_apply_1(x_4, x_1);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_apply_1(x_4, x_1);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
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
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_1, x_6);
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
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
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
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_1, x_6);
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
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(lean_object* x_1) {
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
x_6 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(x_5);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_8; 
lean_free_object(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_11; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_14; 
lean_dec(x_7);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_4, 1);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_Lean_Name_components(x_9);
x_22 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_20, x_21);
x_23 = l_List_append___rarg(x_22, x_18);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = l_Lean_Name_components(x_9);
x_27 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_25, x_26);
x_28 = l_List_append___rarg(x_27, x_24);
lean_ctor_set(x_4, 1, x_28);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_6);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 2);
x_32 = lean_ctor_get(x_4, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_34 = x_7;
} else {
 lean_dec_ref(x_7);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = l_Lean_Name_components(x_9);
x_37 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_35, x_36);
x_38 = l_List_append___rarg(x_37, x_33);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_30);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_31);
lean_ctor_set(x_39, 3, x_32);
if (lean_is_scalar(x_34)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_34;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_6);
return x_40;
}
}
default: 
{
uint8_t x_41; 
lean_dec(x_10);
x_41 = !lean_is_exclusive(x_4);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_4, 1);
lean_dec(x_42);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_7, 1);
x_45 = lean_ctor_get(x_7, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_8, 0);
lean_inc(x_46);
lean_dec(x_8);
x_47 = l_Lean_Name_components(x_9);
x_48 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_46, x_47);
x_49 = l_List_append___rarg(x_48, x_44);
lean_ctor_set(x_4, 1, x_49);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_7, 1);
lean_inc(x_50);
lean_dec(x_7);
x_51 = lean_ctor_get(x_8, 0);
lean_inc(x_51);
lean_dec(x_8);
x_52 = l_Lean_Name_components(x_9);
x_53 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_51, x_52);
x_54 = l_List_append___rarg(x_53, x_50);
lean_ctor_set(x_4, 1, x_54);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_6);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_4, 0);
x_57 = lean_ctor_get(x_4, 2);
x_58 = lean_ctor_get(x_4, 3);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_4);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_60 = x_7;
} else {
 lean_dec_ref(x_7);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_8, 0);
lean_inc(x_61);
lean_dec(x_8);
x_62 = l_Lean_Name_components(x_9);
x_63 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_61, x_62);
x_64 = l_List_append___rarg(x_63, x_59);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_56);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_57);
lean_ctor_set(x_65, 3, x_58);
if (lean_is_scalar(x_60)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_60;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_6);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
x_67 = !lean_is_exclusive(x_7);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_7, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_7, 0);
lean_dec(x_69);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_70; 
lean_dec(x_7);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_4);
lean_ctor_set(x_70, 1, x_6);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_8);
x_71 = !lean_is_exclusive(x_7);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_7, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_7, 0);
lean_dec(x_73);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_74; 
lean_dec(x_7);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_6);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_1, 0);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_1);
x_77 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3(x_76);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
switch (lean_obj_tag(x_82)) {
case 0:
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_81);
lean_dec(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_83 = x_78;
} else {
 lean_dec_ref(x_78);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_75);
lean_ctor_set(x_84, 1, x_77);
return x_84;
}
case 1:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_82);
x_85 = lean_ctor_get(x_75, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_75, 2);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 3);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_78, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_90 = x_78;
} else {
 lean_dec_ref(x_78);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_80, 0);
lean_inc(x_91);
lean_dec(x_80);
x_92 = l_Lean_Name_components(x_81);
x_93 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__1(x_91, x_92);
x_94 = l_List_append___rarg(x_93, x_89);
if (lean_is_scalar(x_88)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_88;
}
lean_ctor_set(x_95, 0, x_85);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_86);
lean_ctor_set(x_95, 3, x_87);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_77);
return x_96;
}
default: 
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_82);
x_97 = lean_ctor_get(x_75, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_75, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_75, 3);
lean_inc(x_99);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 x_100 = x_75;
} else {
 lean_dec_ref(x_75);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_102 = x_78;
} else {
 lean_dec_ref(x_78);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_80, 0);
lean_inc(x_103);
lean_dec(x_80);
x_104 = l_Lean_Name_components(x_81);
x_105 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__2(x_103, x_104);
x_106 = l_List_append___rarg(x_105, x_101);
if (lean_is_scalar(x_100)) {
 x_107 = lean_alloc_ctor(0, 4, 0);
} else {
 x_107 = x_100;
}
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_98);
lean_ctor_set(x_107, 3, x_99);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_77);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_81);
lean_dec(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_109 = x_78;
} else {
 lean_dec_ref(x_78);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_75);
lean_ctor_set(x_110, 1, x_77);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_111 = x_78;
} else {
 lean_dec_ref(x_78);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_75);
lean_ctor_set(x_112, 1, x_77);
return x_112;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___spec__3), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandCompositeFields___closed__1;
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_6(x_2, x_11, x_12, x_10, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, structure has only #");
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
x_1 = lean_mk_string(" fields");
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
x_1 = lean_mk_string("invalid field index, index must be greater than 0");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__5;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_sub(x_42, x_47);
lean_dec(x_42);
x_49 = l_Lean_instInhabitedName;
x_50 = lean_array_get(x_49, x_1, x_48);
lean_dec(x_48);
lean_ctor_set_tag(x_31, 0);
lean_ctor_set(x_31, 1, x_50);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
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
x_51 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_45);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_41, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
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
x_62 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7;
x_63 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_41, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
return x_63;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_68 = lean_ctor_get(x_31, 0);
x_69 = lean_ctor_get(x_31, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_31);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_1);
x_73 = lean_nat_dec_lt(x_72, x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_72);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_69, x_74);
lean_dec(x_69);
x_76 = l_Lean_instInhabitedName;
x_77 = lean_array_get(x_76, x_1, x_75);
lean_dec(x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_30, 0, x_78);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_69);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_79 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_72);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_82 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_68, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_68);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_69);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_90 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7;
x_91 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_68, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_68);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_96 = lean_ctor_get(x_30, 1);
lean_inc(x_96);
lean_dec(x_30);
x_97 = lean_ctor_get(x_31, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_31, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_99 = x_31;
} else {
 lean_dec_ref(x_31);
 x_99 = lean_box(0);
}
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_eq(x_98, x_100);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_array_get_size(x_1);
x_103 = lean_nat_dec_lt(x_102, x_98);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_98, x_104);
lean_dec(x_98);
x_106 = l_Lean_instInhabitedName;
x_107 = lean_array_get(x_106, x_1, x_105);
lean_dec(x_105);
if (lean_is_scalar(x_99)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_99;
 lean_ctor_set_tag(x_108, 0);
}
lean_ctor_set(x_108, 0, x_97);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_96);
lean_ctor_set(x_12, 1, x_109);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_110 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_102);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_113 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_97, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_97);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
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
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_121 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7;
x_122 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_97, x_121, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_97);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_125 = x_122;
} else {
 lean_dec_ref(x_122);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_127 = lean_ctor_get(x_12, 0);
x_128 = lean_ctor_get(x_12, 2);
x_129 = lean_ctor_get(x_12, 3);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_12);
x_130 = lean_ctor_get(x_30, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_131 = x_30;
} else {
 lean_dec_ref(x_30);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_31, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_31, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_134 = x_31;
} else {
 lean_dec_ref(x_31);
 x_134 = lean_box(0);
}
x_135 = lean_unsigned_to_nat(0u);
x_136 = lean_nat_dec_eq(x_133, x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_array_get_size(x_1);
x_138 = lean_nat_dec_lt(x_137, x_133);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_sub(x_133, x_139);
lean_dec(x_133);
x_141 = l_Lean_instInhabitedName;
x_142 = lean_array_get(x_141, x_1, x_140);
lean_dec(x_140);
if (lean_is_scalar(x_134)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_134;
 lean_ctor_set_tag(x_143, 0);
}
lean_ctor_set(x_143, 0, x_132);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_131)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_131;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_130);
x_145 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_145, 0, x_127);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_128);
lean_ctor_set(x_145, 3, x_129);
x_15 = x_145;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_14);
lean_dec(x_13);
x_146 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_137);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__2;
x_149 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__4;
x_151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_132, x_151, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_132);
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
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_14);
lean_dec(x_13);
x_157 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7;
x_158 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_132, x_157, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_132);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_161 = x_158;
} else {
 lean_dec_ref(x_158);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
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
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_apply_8(x_2, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_1, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_free_object(x_1);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_1, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_29 = lean_apply_8(x_2, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_25);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_28);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1___boxed), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_usize(x_1, 2);
lean_dec(x_1);
x_7 = lean_box_usize(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_apply_6(x_2, x_11, x_12, x_10, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields_match__4___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.expandParentFields");
return x_1;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1;
x_3 = lean_unsigned_to_nat(373u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_1, x_6);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_name_mk_string(x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_13 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2;
x_14 = lean_panic_fn(x_12, x_13);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_14);
return x_2;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_1);
x_17 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_1, x_16);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_1);
x_23 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_24 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2;
x_25 = lean_panic_fn(x_23, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a field of structure '");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field '");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' in parent structure");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
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
x_41 = l_Lean_KernelException_toMessageData___closed__3;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2;
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
lean_dec(x_36);
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
x_62 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4;
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_36, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_37);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
x_72 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_36, x_71);
x_73 = l_List_append___rarg(x_72, x_31);
lean_ctor_set(x_13, 1, x_73);
x_16 = x_13;
x_17 = x_10;
goto block_30;
}
}
else
{
lean_object* x_74; 
lean_dec(x_13);
lean_inc(x_2);
x_74 = l_Lean_getPathToBaseStructure_x3f(x_2, x_53, x_38);
lean_dec(x_53);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_37);
x_76 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__1(x_36, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_36);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_37);
x_85 = lean_ctor_get(x_74, 0);
lean_inc(x_85);
lean_dec(x_74);
x_86 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1(x_36, x_85);
x_87 = l_List_append___rarg(x_86, x_31);
x_88 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_88, 0, x_33);
lean_ctor_set(x_88, 1, x_87);
lean_ctor_set(x_88, 2, x_34);
lean_ctor_set(x_88, 3, x_35);
x_16 = x_88;
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
x_18 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___boxed), 10, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_3(x_2, x_7, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_1, x_2, x_8);
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
x_15 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_1, x_2, x_13);
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
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__5(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
}
}
}
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_private.Lean.Elab.StructInst.0.Lean.Elab.Term.StructInst.mkFieldMap");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1;
x_3 = lean_unsigned_to_nat(391u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already beed specified");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_15 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2;
x_16 = lean_panic_fn(x_14, x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_7(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_1 = x_18;
x_2 = x_13;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_dec(x_27);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_box(0);
lean_ctor_set(x_12, 1, x_31);
lean_ctor_set(x_12, 0, x_11);
x_32 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_29, x_12);
x_1 = x_32;
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
lean_ctor_set(x_12, 1, x_35);
lean_ctor_set(x_12, 0, x_11);
x_36 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_29, x_12);
x_1 = x_36;
x_2 = x_28;
goto _start;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
x_41 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_ctor_set(x_12, 1, x_34);
lean_ctor_set(x_12, 0, x_11);
x_43 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_29, x_12);
x_1 = x_43;
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_34);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_28);
lean_free_object(x_12);
lean_dec(x_1);
x_45 = lean_ctor_get(x_11, 0);
lean_inc(x_45);
lean_dec(x_11);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_29);
x_47 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_45, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_45);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_free_object(x_34);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_28);
lean_free_object(x_12);
lean_dec(x_1);
x_56 = lean_ctor_get(x_11, 0);
lean_inc(x_56);
lean_dec(x_11);
x_57 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_57, 0, x_29);
x_58 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_56, x_61, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_56);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
return x_62;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_62);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_34, 0);
x_68 = lean_ctor_get(x_34, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_34);
x_69 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_68);
lean_ctor_set(x_12, 1, x_71);
lean_ctor_set(x_12, 0, x_11);
x_72 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_29, x_12);
x_1 = x_72;
x_2 = x_28;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_28);
lean_free_object(x_12);
lean_dec(x_1);
x_74 = lean_ctor_get(x_11, 0);
lean_inc(x_74);
lean_dec(x_11);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_29);
x_76 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_74, x_79, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_74);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_28);
lean_free_object(x_12);
lean_dec(x_1);
x_85 = lean_ctor_get(x_11, 0);
lean_inc(x_85);
lean_dec(x_11);
x_86 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_86, 0, x_29);
x_87 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_85, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_12);
lean_dec(x_26);
lean_dec(x_11);
lean_dec(x_1);
x_96 = lean_ctor_get(x_2, 1);
lean_inc(x_96);
lean_dec(x_2);
x_97 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_98 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2;
x_99 = lean_panic_fn(x_97, x_98);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_100 = lean_apply_7(x_99, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_1 = x_101;
x_2 = x_96;
x_9 = x_102;
goto _start;
}
else
{
uint8_t x_104; 
lean_dec(x_96);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
return x_100;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_100, 0);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_100);
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
lean_object* x_108; 
x_108 = lean_ctor_get(x_12, 0);
lean_inc(x_108);
lean_dec(x_12);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_1, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_11);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_110, x_113);
x_1 = x_114;
x_2 = x_109;
goto _start;
}
else
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
lean_dec(x_111);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_11);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_110, x_118);
x_1 = x_119;
x_2 = x_109;
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_123 = x_116;
} else {
 lean_dec_ref(x_116);
 x_123 = lean_box(0);
}
x_124 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_124 == 0)
{
uint8_t x_125; 
x_125 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_121);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_122);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_11);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__3(x_1, x_110, x_127);
x_1 = x_128;
x_2 = x_109;
goto _start;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_109);
lean_dec(x_1);
x_130 = lean_ctor_get(x_11, 0);
lean_inc(x_130);
lean_dec(x_11);
x_131 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_131, 0, x_110);
x_132 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_135 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_130, x_135, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_130);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_109);
lean_dec(x_1);
x_141 = lean_ctor_get(x_11, 0);
lean_inc(x_141);
lean_dec(x_11);
x_142 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_142, 0, x_110);
x_143 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6;
x_146 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_141, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_141);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_108);
lean_dec(x_11);
lean_dec(x_1);
x_152 = lean_ctor_get(x_2, 1);
lean_inc(x_152);
lean_dec(x_2);
x_153 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_154 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2;
x_155 = lean_panic_fn(x_153, x_154);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_156 = lean_apply_7(x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_1 = x_157;
x_2 = x_152;
x_9 = x_158;
goto _start;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_152);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_156, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_162 = x_156;
} else {
 lean_dec_ref(x_156);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1;
x_10 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
uint8_t l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string("' is not a valid field of '");
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_array_get_size(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findIdx_x3f_loop___rarg(x_2, x_11, x_12, x_13, lean_box(0));
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
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
x_22 = l_Lean_KernelException_toMessageData___closed__3;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2);
x_6 = l_Lean_Syntax_mkAntiquotNode___closed__9;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_mkProj(x_1, x_17, x_14);
if (lean_obj_tag(x_13) == 1)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_array_fget(x_20, x_22);
x_25 = lean_box(0);
x_26 = lean_array_fset(x_20, x_22, x_25);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_24, x_3);
x_28 = lean_array_fset(x_26, x_22, x_27);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_3);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_34);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_array_fget(x_30, x_32);
x_36 = lean_box(0);
x_37 = lean_array_fset(x_30, x_32, x_36);
x_38 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_35, x_3);
x_39 = lean_array_fset(x_37, x_32, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_40);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
}
else
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
x_43 = l_Lean_mkProj(x_1, x_41, x_14);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_13, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_46 = x_13;
} else {
 lean_dec_ref(x_13);
 x_46 = lean_box(0);
}
x_47 = lean_array_get_size(x_45);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
if (lean_is_scalar(x_46)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_46;
}
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_50);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_4);
lean_ctor_set(x_51, 1, x_42);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_array_fget(x_45, x_48);
x_53 = lean_box(0);
x_54 = lean_array_fset(x_45, x_48, x_53);
x_55 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_52, x_3);
x_56 = lean_array_fset(x_54, x_48, x_55);
if (lean_is_scalar(x_46)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_46;
}
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_4, 1, x_43);
lean_ctor_set(x_4, 0, x_57);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_43);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_42);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_15);
if (x_60 == 0)
{
return x_15;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_15, 0);
x_62 = lean_ctor_get(x_15, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_15);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_4, 0);
x_65 = lean_ctor_get(x_4, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_66 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = l_Lean_mkProj(x_1, x_67, x_65);
if (lean_obj_tag(x_64) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_74 = lean_array_get_size(x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_nat_dec_lt(x_75, x_74);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
if (lean_is_scalar(x_73)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_73;
}
lean_ctor_set(x_77, 0, x_71);
lean_ctor_set(x_77, 1, x_72);
x_78 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_69;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_68);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_80 = lean_array_fget(x_72, x_75);
x_81 = lean_box(0);
x_82 = lean_array_fset(x_72, x_75, x_81);
x_83 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_80, x_3);
x_84 = lean_array_fset(x_82, x_75, x_83);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_71);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_69;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_68);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
x_88 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_70);
if (lean_is_scalar(x_69)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_69;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_68);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_3);
lean_dec(x_1);
x_90 = lean_ctor_get(x_66, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_66, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_92 = x_66;
} else {
 lean_dec_ref(x_66);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_4);
lean_ctor_set(x_94, 1, x_11);
return x_94;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_List_tail_x21___rarg(x_3);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_9 = l_List_tail_x21___rarg(x_6);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_2);
x_4 = l_Lean_Syntax_mkApp___closed__1;
x_5 = lean_array_push(x_4, x_3);
x_6 = lean_array_push(x_5, x_1);
x_7 = l_Lean_nullKind;
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_instInhabitedField(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkOptionalNode___closed__1;
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__2), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1;
lean_inc(x_16);
x_19 = l_List_map___rarg(x_18, x_16);
x_20 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_8);
lean_inc(x_15);
lean_inc(x_2);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_2, x_3, x_15, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2;
x_26 = l_List_head_x21___rarg(x_25, x_16);
lean_dec(x_16);
x_27 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_mkOptionalNode___closed__1;
x_30 = l_Lean_Syntax_setArg(x_5, x_28, x_29);
x_31 = l_List_redLength___rarg(x_19);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
x_33 = l_List_toArrayAux___rarg(x_19, x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_36 = 0;
x_37 = x_33;
x_38 = l_Id_instMonadId;
x_39 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3;
x_40 = l_Array_mapMUnsafe_map___rarg(x_38, x_39, x_35, x_36, x_37);
x_41 = x_40;
x_42 = l_Lean_nullKind;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_unsigned_to_nat(2u);
x_45 = l_Lean_Syntax_setArg(x_30, x_44, x_43);
x_46 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_45, x_23);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_26, 1);
x_49 = lean_ctor_get(x_26, 2);
lean_dec(x_49);
x_50 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_51 = l_List_head_x21___rarg(x_50, x_48);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_26, 2, x_54);
lean_ctor_set(x_26, 1, x_53);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_55 = lean_ctor_get(x_26, 0);
x_56 = lean_ctor_get(x_26, 1);
x_57 = lean_ctor_get(x_26, 3);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_26);
x_58 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_59 = l_List_head_x21___rarg(x_58, x_56);
lean_dec(x_56);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_46);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_55);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_57);
lean_ctor_set(x_21, 0, x_63);
return x_21;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_21);
x_64 = lean_ctor_get(x_27, 0);
lean_inc(x_64);
lean_dec(x_27);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_19);
lean_ctor_set(x_65, 3, x_23);
x_66 = lean_apply_8(x_6, x_65, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_26);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_66, 0);
x_70 = lean_ctor_get(x_26, 1);
x_71 = lean_ctor_get(x_26, 2);
lean_dec(x_71);
x_72 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_73 = l_List_head_x21___rarg(x_72, x_70);
lean_dec(x_70);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_26, 2, x_76);
lean_ctor_set(x_26, 1, x_75);
lean_ctor_set(x_66, 0, x_26);
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_26, 0);
x_79 = lean_ctor_get(x_26, 1);
x_80 = lean_ctor_get(x_26, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_26);
x_81 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_82 = l_List_head_x21___rarg(x_81, x_79);
lean_dec(x_79);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_77);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_84);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_80);
lean_ctor_set(x_66, 0, x_86);
return x_66;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_66, 0);
x_88 = lean_ctor_get(x_66, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_66);
x_89 = lean_ctor_get(x_26, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_26, 3);
lean_inc(x_91);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 x_92 = x_26;
} else {
 lean_dec_ref(x_26);
 x_92 = lean_box(0);
}
x_93 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_94 = l_List_head_x21___rarg(x_93, x_90);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_87);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(0, 4, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_89);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_98, 2, x_97);
lean_ctor_set(x_98, 3, x_91);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_88);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_26);
x_100 = !lean_is_exclusive(x_66);
if (x_100 == 0)
{
return x_66;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_66, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_66);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_21, 0);
x_105 = lean_ctor_get(x_21, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_21);
x_106 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2;
x_107 = l_List_head_x21___rarg(x_106, x_16);
lean_dec(x_16);
x_108 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; size_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_109 = lean_unsigned_to_nat(4u);
x_110 = l_Lean_mkOptionalNode___closed__1;
x_111 = l_Lean_Syntax_setArg(x_5, x_109, x_110);
x_112 = l_List_redLength___rarg(x_19);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
x_114 = l_List_toArrayAux___rarg(x_19, x_113);
x_115 = lean_array_get_size(x_114);
x_116 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_117 = 0;
x_118 = x_114;
x_119 = l_Id_instMonadId;
x_120 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3;
x_121 = l_Array_mapMUnsafe_map___rarg(x_119, x_120, x_116, x_117, x_118);
x_122 = x_121;
x_123 = l_Lean_nullKind;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_unsigned_to_nat(2u);
x_126 = l_Lean_Syntax_setArg(x_111, x_125, x_124);
x_127 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_126, x_104);
x_128 = lean_ctor_get(x_107, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_107, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_107, 3);
lean_inc(x_130);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 x_131 = x_107;
} else {
 lean_dec_ref(x_107);
 x_131 = lean_box(0);
}
x_132 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_133 = l_List_head_x21___rarg(x_132, x_129);
lean_dec(x_129);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_127);
if (lean_is_scalar(x_131)) {
 x_137 = lean_alloc_ctor(0, 4, 0);
} else {
 x_137 = x_131;
}
lean_ctor_set(x_137, 0, x_128);
lean_ctor_set(x_137, 1, x_135);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_130);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_105);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_108, 0);
lean_inc(x_139);
lean_dec(x_108);
x_140 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_140, 0, x_5);
lean_ctor_set(x_140, 1, x_139);
lean_ctor_set(x_140, 2, x_19);
lean_ctor_set(x_140, 3, x_104);
x_141 = lean_apply_8(x_6, x_140, x_8, x_9, x_10, x_11, x_12, x_13, x_105);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_144 = x_141;
} else {
 lean_dec_ref(x_141);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_107, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_107, 1);
lean_inc(x_146);
x_147 = lean_ctor_get(x_107, 3);
lean_inc(x_147);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 lean_ctor_release(x_107, 2);
 lean_ctor_release(x_107, 3);
 x_148 = x_107;
} else {
 lean_dec_ref(x_107);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_150 = l_List_head_x21___rarg(x_149, x_146);
lean_dec(x_146);
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_142);
if (lean_is_scalar(x_148)) {
 x_154 = lean_alloc_ctor(0, 4, 0);
} else {
 x_154 = x_148;
}
lean_ctor_set(x_154, 0, x_145);
lean_ctor_set(x_154, 1, x_152);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_147);
if (lean_is_scalar(x_144)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_144;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_143);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_107);
x_156 = lean_ctor_get(x_141, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_141, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_158 = x_141;
} else {
 lean_dec_ref(x_141);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_160 = !lean_is_exclusive(x_21);
if (x_160 == 0)
{
return x_21;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_21, 0);
x_162 = lean_ctor_get(x_21, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_21);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_164 = lean_ctor_get(x_17, 0);
lean_inc(x_164);
lean_dec(x_17);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_14);
return x_165;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___boxed), 14, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
x_20 = l_Std_HashMap_toList___rarg(x_17);
lean_dec(x_17);
x_21 = l_List_mapM___rarg(x_7, lean_box(0), lean_box(0), x_19, x_20);
x_22 = lean_apply_7(x_21, x_9, x_10, x_11, x_12, x_13, x_14, x_18);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_14);
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
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_14);
lean_inc(x_13);
x_15 = l_Lean_getStructureFields(x_13, x_14);
x_16 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
x_17 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_inc(x_16);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__4), 15, 7);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_13);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_1);
lean_closure_set(x_18, 6, x_17);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_20);
lean_dec(x_16);
lean_ctor_set(x_7, 3, x_21);
x_22 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_23 = lean_apply_7(x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
x_26 = lean_ctor_get(x_7, 2);
x_27 = lean_ctor_get(x_7, 3);
x_28 = lean_ctor_get(x_7, 4);
x_29 = lean_ctor_get(x_7, 5);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_16, x_27);
lean_dec(x_27);
lean_dec(x_16);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_31, 2, x_26);
lean_ctor_set(x_31, 3, x_30);
lean_ctor_set(x_31, 4, x_28);
lean_ctor_set(x_31, 5, x_29);
x_32 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_33 = lean_apply_7(x_32, x_3, x_4, x_5, x_6, x_31, x_8, x_12);
return x_33;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_findField_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_List_find_x3f___rarg(x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_2(x_4, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_8);
x_17 = l_Lean_Elab_Term_StructInst_findField_x3f(x_16, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_inc(x_8);
lean_inc(x_3);
x_18 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
x_19 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_box(2);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_8);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_15);
return x_27;
}
case 1:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_19);
x_28 = l_Lean_mkHole(x_4);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_inc(x_4);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_8);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_29);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_15);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_19, 0);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_37, x_38);
lean_dec(x_37);
lean_inc(x_8);
x_40 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_39, x_8);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_7);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_15);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_18, 0);
lean_inc(x_49);
lean_dec(x_18);
x_50 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_9);
lean_inc(x_8);
x_51 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_3, x_5, x_8, x_50, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
lean_inc(x_4);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_4);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_54);
lean_ctor_set(x_55, 3, x_52);
x_56 = lean_apply_8(x_6, x_55, x_9, x_10, x_11, x_12, x_13, x_14, x_53);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_inc(x_4);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_4);
lean_ctor_set(x_60, 1, x_8);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_54);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_7);
lean_ctor_set(x_56, 0, x_64);
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_ctor_get(x_56, 0);
x_66 = lean_ctor_get(x_56, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_56);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_65);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_8);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_54);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_67);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_7);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_66);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_56);
if (x_74 == 0)
{
return x_56;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_56, 0);
x_76 = lean_ctor_get(x_56, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_56);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_49);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_51);
if (x_78 == 0)
{
return x_51;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_51, 0);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_51);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_82 = lean_ctor_get(x_17, 0);
lean_inc(x_82);
lean_dec(x_17);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_7);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_15);
return x_84;
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_15);
lean_inc(x_14);
x_16 = l_Lean_getStructureFields(x_14, x_15);
x_17 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
lean_inc(x_16);
lean_inc(x_17);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1___boxed), 15, 6);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_14);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_17);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_1);
x_19 = lean_box(0);
x_20 = lean_array_get_size(x_16);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_23 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_24 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_23);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 3);
x_27 = l_Lean_replaceRef(x_17, x_26);
lean_dec(x_26);
lean_dec(x_17);
lean_ctor_set(x_7, 3, x_27);
x_28 = lean_nat_dec_le(x_20, x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_30 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_29);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_10);
x_31 = 0;
x_32 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_33 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_34 = l_Array_foldlMUnsafe_fold___rarg(x_33, x_18, x_16, x_31, x_32, x_19);
x_35 = lean_apply_7(x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = l_List_reverse___rarg(x_37);
x_39 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_38);
lean_ctor_set(x_35, 0, x_39);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = l_List_reverse___rarg(x_40);
x_43 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_49 = lean_ctor_get(x_7, 0);
x_50 = lean_ctor_get(x_7, 1);
x_51 = lean_ctor_get(x_7, 2);
x_52 = lean_ctor_get(x_7, 3);
x_53 = lean_ctor_get(x_7, 4);
x_54 = lean_ctor_get(x_7, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_7);
x_55 = l_Lean_replaceRef(x_17, x_52);
lean_dec(x_52);
lean_dec(x_17);
x_56 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_51);
lean_ctor_set(x_56, 3, x_55);
lean_ctor_set(x_56, 4, x_53);
lean_ctor_set(x_56, 5, x_54);
x_57 = lean_nat_dec_le(x_20, x_20);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_59 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_58);
lean_ctor_set(x_10, 0, x_59);
return x_10;
}
else
{
size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_free_object(x_10);
x_60 = 0;
x_61 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_62 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_63 = l_Array_foldlMUnsafe_fold___rarg(x_62, x_18, x_16, x_60, x_61, x_19);
x_64 = lean_apply_7(x_63, x_3, x_4, x_5, x_6, x_56, x_8, x_13);
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
x_69 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_68);
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
lean_dec(x_2);
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
x_75 = lean_ctor_get(x_10, 0);
x_76 = lean_ctor_get(x_10, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_10);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_78);
lean_inc(x_77);
x_79 = l_Lean_getStructureFields(x_77, x_78);
x_80 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
lean_inc(x_79);
lean_inc(x_80);
lean_inc(x_2);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1___boxed), 15, 6);
lean_closure_set(x_81, 0, x_2);
lean_closure_set(x_81, 1, x_77);
lean_closure_set(x_81, 2, x_78);
lean_closure_set(x_81, 3, x_80);
lean_closure_set(x_81, 4, x_79);
lean_closure_set(x_81, 5, x_1);
x_82 = lean_box(0);
x_83 = lean_array_get_size(x_79);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_87 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_89 = lean_ctor_get(x_7, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_7, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_7, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_7, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_7, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_7, 5);
lean_inc(x_94);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 lean_ctor_release(x_7, 2);
 lean_ctor_release(x_7, 3);
 lean_ctor_release(x_7, 4);
 lean_ctor_release(x_7, 5);
 x_95 = x_7;
} else {
 lean_dec_ref(x_7);
 x_95 = lean_box(0);
}
x_96 = l_Lean_replaceRef(x_80, x_92);
lean_dec(x_92);
lean_dec(x_80);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 6, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_89);
lean_ctor_set(x_97, 1, x_90);
lean_ctor_set(x_97, 2, x_91);
lean_ctor_set(x_97, 3, x_96);
lean_ctor_set(x_97, 4, x_93);
lean_ctor_set(x_97, 5, x_94);
x_98 = lean_nat_dec_le(x_83, x_83);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_79);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_100 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_76);
return x_101;
}
else
{
size_t x_102; size_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = 0;
x_103 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_104 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_105 = l_Array_foldlMUnsafe_fold___rarg(x_104, x_81, x_79, x_102, x_103, x_82);
x_106 = lean_apply_7(x_105, x_3, x_4, x_5, x_6, x_97, x_8, x_76);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_List_reverse___rarg(x_107);
x_111 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_2);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_115 = x_106;
} else {
 lean_dec_ref(x_106);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(lean_object* x_1) {
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
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_List_tail_x21___rarg(x_7);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_8);
x_9 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(x_6);
lean_ctor_set(x_1, 1, x_9);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_4);
x_15 = l_List_tail_x21___rarg(x_12);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
x_17 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(x_10);
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_16);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 3);
lean_inc(x_23);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 lean_ctor_release(x_18, 2);
 lean_ctor_release(x_18, 3);
 x_24 = x_18;
} else {
 lean_dec_ref(x_18);
 x_24 = lean_box(0);
}
x_25 = l_List_tail_x21___rarg(x_21);
lean_dec(x_21);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 4, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
x_27 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2;
x_3 = l_List_head_x21___rarg___closed__3;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_10);
x_12 = l_Lean_Syntax_mkApp___closed__1;
x_13 = lean_array_push(x_12, x_11);
lean_inc(x_1);
x_14 = lean_array_push(x_13, x_1);
x_15 = l_Lean_nullKind;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = 1;
x_18 = x_3 + x_17;
x_19 = x_16;
x_20 = lean_array_uset(x_9, x_3, x_19);
x_3 = x_18;
x_4 = x_20;
goto _start;
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS;
x_3 = l_List_head_x21___rarg___closed__3;
x_4 = lean_panic_fn(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7(x_4, x_6);
lean_dec(x_6);
x_8 = 1;
x_9 = x_2 + x_8;
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
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_6, 0);
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_20);
x_22 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(x_20);
x_23 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_3, x_4, x_19, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3(x_20);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_31 = l_Lean_Syntax_setArg(x_5, x_29, x_30);
x_32 = l_List_redLength___rarg(x_22);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___rarg(x_22, x_33);
x_35 = lean_array_get_size(x_34);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
x_38 = x_34;
x_39 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4(x_30, x_36, x_37, x_38);
x_40 = x_39;
x_41 = l_Lean_nullKind;
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_unsigned_to_nat(2u);
x_44 = l_Lean_Syntax_setArg(x_31, x_43, x_42);
x_45 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_44, x_25);
x_46 = !lean_is_exclusive(x_27);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_27, 1);
x_48 = lean_ctor_get(x_27, 2);
lean_dec(x_48);
x_49 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_47);
lean_dec(x_47);
x_50 = lean_box(0);
lean_ctor_set(x_6, 1, x_50);
lean_ctor_set(x_6, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_27, 2, x_51);
lean_ctor_set(x_27, 1, x_6);
x_52 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_27);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_27);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_27);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_27, 0);
x_65 = lean_ctor_get(x_27, 1);
x_66 = lean_ctor_get(x_27, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_27);
x_67 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_65);
lean_dec(x_65);
x_68 = lean_box(0);
lean_ctor_set(x_6, 1, x_68);
lean_ctor_set(x_6, 0, x_67);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_45);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_6);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_66);
x_71 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
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
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_72);
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
lean_dec(x_70);
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
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_28, 0);
lean_inc(x_81);
lean_dec(x_28);
lean_inc(x_5);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_5);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_22);
lean_ctor_set(x_82, 3, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_83 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_82, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = !lean_is_exclusive(x_27);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_87 = lean_ctor_get(x_27, 1);
x_88 = lean_ctor_get(x_27, 2);
lean_dec(x_88);
x_89 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_87);
lean_dec(x_87);
x_90 = lean_box(0);
lean_ctor_set(x_6, 1, x_90);
lean_ctor_set(x_6, 0, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_27, 2, x_91);
lean_ctor_set(x_27, 1, x_6);
x_92 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_85);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_27);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_92, 0);
x_97 = lean_ctor_get(x_92, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_27);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_27);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
return x_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_27, 0);
x_105 = lean_ctor_get(x_27, 1);
x_106 = lean_ctor_get(x_27, 3);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_27);
x_107 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_105);
lean_dec(x_105);
x_108 = lean_box(0);
lean_ctor_set(x_6, 1, x_108);
lean_ctor_set(x_6, 0, x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_84);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_104);
lean_ctor_set(x_110, 1, x_6);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_106);
x_111 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_85);
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
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_110);
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
lean_dec(x_110);
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
}
else
{
uint8_t x_121; 
lean_dec(x_27);
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_83);
if (x_121 == 0)
{
return x_83;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_83, 0);
x_123 = lean_ctor_get(x_83, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_83);
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
uint8_t x_125; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_free_object(x_6);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_125 = !lean_is_exclusive(x_24);
if (x_125 == 0)
{
return x_24;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_24, 0);
x_127 = lean_ctor_get(x_24, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_24);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_20);
lean_dec(x_19);
x_129 = lean_ctor_get(x_21, 0);
lean_inc(x_129);
lean_dec(x_21);
x_130 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_130, 0);
lean_ctor_set(x_6, 1, x_132);
lean_ctor_set(x_6, 0, x_129);
lean_ctor_set(x_130, 0, x_6);
return x_130;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_130, 0);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_130);
lean_ctor_set(x_6, 1, x_133);
lean_ctor_set(x_6, 0, x_129);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_6);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_129);
lean_free_object(x_6);
x_136 = !lean_is_exclusive(x_130);
if (x_136 == 0)
{
return x_130;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_130, 0);
x_138 = lean_ctor_get(x_130, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_130);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_6, 0);
x_141 = lean_ctor_get(x_6, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_6);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_isSimpleField_x3f(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_inc(x_143);
x_145 = l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__2(x_143);
x_146 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_142);
lean_inc(x_3);
x_147 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_3, x_4, x_142, x_146, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3(x_143);
lean_dec(x_143);
lean_inc(x_3);
lean_inc(x_2);
x_151 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_142);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; size_t x_159; size_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_152 = lean_unsigned_to_nat(4u);
x_153 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_154 = l_Lean_Syntax_setArg(x_5, x_152, x_153);
x_155 = l_List_redLength___rarg(x_145);
x_156 = lean_mk_empty_array_with_capacity(x_155);
lean_dec(x_155);
x_157 = l_List_toArrayAux___rarg(x_145, x_156);
x_158 = lean_array_get_size(x_157);
x_159 = lean_usize_of_nat(x_158);
lean_dec(x_158);
x_160 = 0;
x_161 = x_157;
x_162 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4(x_153, x_159, x_160, x_161);
x_163 = x_162;
x_164 = l_Lean_nullKind;
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
x_166 = lean_unsigned_to_nat(2u);
x_167 = l_Lean_Syntax_setArg(x_154, x_166, x_165);
x_168 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_167, x_148);
x_169 = lean_ctor_get(x_150, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_150, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_150, 3);
lean_inc(x_171);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 x_172 = x_150;
} else {
 lean_dec_ref(x_150);
 x_172 = lean_box(0);
}
x_173 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_170);
lean_dec(x_170);
x_174 = lean_box(0);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_176, 0, x_168);
if (lean_is_scalar(x_172)) {
 x_177 = lean_alloc_ctor(0, 4, 0);
} else {
 x_177 = x_172;
}
lean_ctor_set(x_177, 0, x_169);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_171);
x_178 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_141, x_7, x_8, x_9, x_10, x_11, x_12, x_149);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_177);
lean_ctor_set(x_182, 1, x_179);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_177);
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_178, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_186 = x_178;
} else {
 lean_dec_ref(x_178);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_151, 0);
lean_inc(x_188);
lean_dec(x_151);
lean_inc(x_5);
x_189 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_189, 0, x_5);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_189, 2, x_145);
lean_ctor_set(x_189, 3, x_148);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_190 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_189, x_7, x_8, x_9, x_10, x_11, x_12, x_149);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_150, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_150, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_150, 3);
lean_inc(x_195);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 lean_ctor_release(x_150, 2);
 lean_ctor_release(x_150, 3);
 x_196 = x_150;
} else {
 lean_dec_ref(x_150);
 x_196 = lean_box(0);
}
x_197 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_194);
lean_dec(x_194);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_191);
if (lean_is_scalar(x_196)) {
 x_201 = lean_alloc_ctor(0, 4, 0);
} else {
 x_201 = x_196;
}
lean_ctor_set(x_201, 0, x_193);
lean_ctor_set(x_201, 1, x_199);
lean_ctor_set(x_201, 2, x_200);
lean_ctor_set(x_201, 3, x_195);
x_202 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_141, x_7, x_8, x_9, x_10, x_11, x_12, x_192);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_201);
lean_ctor_set(x_206, 1, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_201);
x_208 = lean_ctor_get(x_202, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_202, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_210 = x_202;
} else {
 lean_dec_ref(x_202);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_150);
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_212 = lean_ctor_get(x_190, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_190, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_214 = x_190;
} else {
 lean_dec_ref(x_190);
 x_214 = lean_box(0);
}
if (lean_is_scalar(x_214)) {
 x_215 = lean_alloc_ctor(1, 2, 0);
} else {
 x_215 = x_214;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_213);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_145);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_216 = lean_ctor_get(x_147, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_147, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_218 = x_147;
} else {
 lean_dec_ref(x_147);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_143);
lean_dec(x_142);
x_220 = lean_ctor_get(x_144, 0);
lean_inc(x_220);
lean_dec(x_144);
x_221 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_141, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_224 = x_221;
} else {
 lean_dec_ref(x_221);
 x_224 = lean_box(0);
}
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_220);
lean_ctor_set(x_225, 1, x_222);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_223);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_220);
x_227 = lean_ctor_get(x_221, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_221, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_229 = x_221;
} else {
 lean_dec_ref(x_221);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6(x_15);
lean_dec(x_15);
x_18 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_getStructureFields(x_12, x_13);
x_15 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1___boxed), 13, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_ctor_set(x_6, 3, x_19);
x_20 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 2);
x_24 = lean_ctor_get(x_6, 3);
x_25 = lean_ctor_get(x_6, 4);
x_26 = lean_ctor_get(x_6, 5);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_27 = l_Lean_replaceRef(x_15, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_25);
lean_ctor_set(x_28, 5, x_26);
x_29 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__4(x_1, x_16, x_2, x_3, x_4, x_5, x_28, x_7, x_11);
return x_29;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, size_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_7 == x_8;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_uget(x_6, x_7);
x_19 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_18);
x_20 = l_Lean_Elab_Term_StructInst_findField_x3f(x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_2);
x_21 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_23 = lean_box(2);
lean_inc(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_18);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
lean_inc(x_5);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_23);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_9);
x_30 = 1;
x_31 = x_7 + x_30;
x_7 = x_31;
x_9 = x_29;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
lean_dec(x_22);
x_33 = l_Lean_mkHole(x_5);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_5);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_18);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
lean_inc(x_5);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_9);
x_41 = 1;
x_42 = x_7 + x_41;
x_7 = x_42;
x_9 = x_40;
goto _start;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_44 = lean_ctor_get(x_22, 0);
lean_inc(x_44);
lean_dec(x_22);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getArg(x_44, x_45);
lean_dec(x_44);
lean_inc(x_18);
x_47 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkProjStx(x_46, x_18);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_5);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
lean_inc(x_5);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_9);
x_55 = 1;
x_56 = x_7 + x_55;
x_7 = x_56;
x_9 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
lean_inc(x_58);
lean_dec(x_21);
x_59 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_10);
lean_inc(x_18);
lean_inc(x_3);
x_60 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkSubstructSource(x_3, x_4, x_18, x_59, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
lean_inc(x_5);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_58);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_61);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_65 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_64, x_10, x_11, x_12, x_13, x_14, x_15, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_66);
lean_inc(x_5);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_5);
lean_ctor_set(x_69, 1, x_18);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_63);
x_71 = lean_box(0);
lean_inc(x_5);
x_72 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_72, 2, x_68);
lean_ctor_set(x_72, 3, x_71);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_9);
x_74 = 1;
x_75 = x_7 + x_74;
x_7 = x_75;
x_9 = x_73;
x_16 = x_67;
goto _start;
}
else
{
uint8_t x_77; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_65);
if (x_77 == 0)
{
return x_65;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_65, 0);
x_79 = lean_ctor_get(x_65, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_65);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_58);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_60);
if (x_81 == 0)
{
return x_60;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_60, 0);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_60);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; 
lean_dec(x_18);
x_85 = lean_ctor_get(x_20, 0);
lean_inc(x_85);
lean_dec(x_20);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_9);
x_87 = 1;
x_88 = x_7 + x_87;
x_7 = x_88;
x_9 = x_86;
goto _start;
}
}
else
{
lean_object* x_90; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_9);
lean_ctor_set(x_90, 1, x_16);
return x_90;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
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
x_17 = lean_box(0);
x_18 = lean_array_get_size(x_15);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_22 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_21);
lean_ctor_set(x_9, 0, x_22);
return x_9;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_6, 3);
x_25 = l_Lean_replaceRef(x_16, x_24);
lean_dec(x_24);
lean_ctor_set(x_6, 3, x_25);
x_26 = lean_nat_dec_le(x_18, x_18);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_6);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_28 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_27);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
lean_free_object(x_9);
x_29 = 0;
x_30 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_31 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(x_1, x_13, x_14, x_15, x_16, x_15, x_29, x_30, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = l_List_reverse___rarg(x_33);
x_35 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = l_List_reverse___rarg(x_36);
x_39 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = lean_ctor_get(x_6, 1);
x_47 = lean_ctor_get(x_6, 2);
x_48 = lean_ctor_get(x_6, 3);
x_49 = lean_ctor_get(x_6, 4);
x_50 = lean_ctor_get(x_6, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_6);
x_51 = l_Lean_replaceRef(x_16, x_48);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_51);
lean_ctor_set(x_52, 4, x_49);
lean_ctor_set(x_52, 5, x_50);
x_53 = lean_nat_dec_le(x_18, x_18);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_52);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_55 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_54);
lean_ctor_set(x_9, 0, x_55);
return x_9;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
lean_free_object(x_9);
x_56 = 0;
x_57 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_58 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(x_1, x_13, x_14, x_15, x_16, x_15, x_56, x_57, x_17, x_2, x_3, x_4, x_5, x_52, x_7, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = l_List_reverse___rarg(x_59);
x_63 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_65 = lean_ctor_get(x_58, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_58, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_67 = x_58;
} else {
 lean_dec_ref(x_58);
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
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_72);
lean_inc(x_71);
x_73 = l_Lean_getStructureFields(x_71, x_72);
x_74 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_75 = lean_box(0);
x_76 = lean_array_get_size(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_lt(x_77, x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_79 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_80 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_70);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_82 = lean_ctor_get(x_6, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_6, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_6, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_6, 4);
lean_inc(x_86);
x_87 = lean_ctor_get(x_6, 5);
lean_inc(x_87);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 x_88 = x_6;
} else {
 lean_dec_ref(x_6);
 x_88 = lean_box(0);
}
x_89 = l_Lean_replaceRef(x_74, x_85);
lean_dec(x_85);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 6, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_82);
lean_ctor_set(x_90, 1, x_83);
lean_ctor_set(x_90, 2, x_84);
lean_ctor_set(x_90, 3, x_89);
lean_ctor_set(x_90, 4, x_86);
lean_ctor_set(x_90, 5, x_87);
x_91 = lean_nat_dec_le(x_76, x_76);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1;
x_93 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_70);
return x_94;
}
else
{
size_t x_95; size_t x_96; lean_object* x_97; 
x_95 = 0;
x_96 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_97 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(x_1, x_71, x_72, x_73, x_74, x_73, x_95, x_96, x_75, x_2, x_3, x_4, x_5, x_90, x_7, x_70);
lean_dec(x_73);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_101 = l_List_reverse___rarg(x_98);
x_102 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_101);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_17 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__10(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
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
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__4(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__8(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_19 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_19;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_CtorHeaderResult_instMVars___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(x_1);
if (lean_obj_tag(x_4) == 3)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__1___rarg(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
x_11 = lean_apply_4(x_6, x_10, x_2, x_3, x_4);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_apply_3(x_5, x_2, x_3, x_4);
return x_12;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux_match__3___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
x_1 = lean_mk_string("unexpected constructor type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_1, x_14);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_16 = l_Lean_Meta_whnfForall(x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_17, sizeof(void*)*3);
lean_dec(x_17);
x_22 = (uint8_t)((x_21 << 24) >> 61);
x_23 = lean_box(x_22);
if (lean_obj_tag(x_23) == 3)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = 1;
x_26 = lean_box(0);
lean_inc(x_7);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_24, x_25, x_26, x_7, x_8, x_9, x_10, x_18);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_expr_instantiate1(x_20, x_28);
lean_dec(x_20);
lean_inc(x_28);
x_31 = l_Lean_mkApp(x_3, x_28);
x_32 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
x_33 = lean_array_push(x_4, x_32);
x_1 = x_15;
x_2 = x_30;
x_3 = x_31;
x_4 = x_33;
x_11 = x_29;
goto _start;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_19);
x_36 = 0;
x_37 = lean_box(0);
lean_inc(x_7);
x_38 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_35, x_36, x_37, x_7, x_8, x_9, x_10, x_18);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_expr_instantiate1(x_20, x_39);
lean_dec(x_20);
x_42 = l_Lean_mkApp(x_3, x_39);
x_1 = x_15;
x_2 = x_41;
x_3 = x_42;
x_11 = x_40;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_dec(x_16);
x_45 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3;
x_46 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1(x_45, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_2);
lean_ctor_set(x_51, 2, x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_11);
return x_52;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_14 = lean_box_uint64(x_13);
x_15 = lean_apply_5(x_3, x_9, x_10, x_11, x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_apply_2(x_4, x_9, x_2);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_apply_1(x_5, x_2);
return x_17;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody_match__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getForallBody(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_1, 1, x_19);
lean_ctor_set(x_1, 0, x_15);
lean_ctor_set(x_17, 0, x_1);
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
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_5, x_6, x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_13);
x_16 = l_Lean_mkConst(x_15, x_13);
lean_inc(x_1);
x_17 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_17, 0, x_1);
x_18 = lean_instantiate_type_lparams(x_17, x_13);
lean_dec(x_13);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = l_Array_empty___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux(x_19, x_18, x_16, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_propagateExpectedType(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = l_Lean_Elab_Term_synthesizeAppInstMVars(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_22);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_22);
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
else
{
uint8_t x_38; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstDefault");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_mkAnnotation(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
x_3 = l_Lean_annotation_x3f(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1(lean_object* x_1) {
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
x_1 = lean_mk_string("failed to elaborate field '");
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
x_1 = lean_mk_string("' of '");
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
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_18 = l_Lean_Meta_SynthInstance_getInstances___lambda__1___closed__8;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = l_Lean_KernelException_toMessageData___closed__15;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg(x_22, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_throwFailedToElabField___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__3___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__6___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__7___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct_match__8___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 3);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 3, x_12);
x_13 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_20 = l_Lean_replaceRef(x_1, x_17);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_18);
lean_ctor_set(x_21, 5, x_19);
x_22 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2(x_2, x_3, x_4, x_5, x_6, x_21, x_8, x_9);
lean_dec(x_21);
return x_22;
}
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 5);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_st_ref_get(x_7, x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_take(x_3, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 5);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_26, 1);
x_32 = l_Std_PersistentArray_push___rarg(x_31, x_1);
lean_ctor_set(x_26, 1, x_32);
x_33 = lean_st_ref_set(x_3, x_25, x_27);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
x_43 = l_Std_PersistentArray_push___rarg(x_42, x_1);
x_44 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*2, x_40);
lean_ctor_set(x_25, 5, x_44);
x_45 = lean_st_ref_set(x_3, x_25, x_27);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
x_52 = lean_ctor_get(x_25, 2);
x_53 = lean_ctor_get(x_25, 3);
x_54 = lean_ctor_get(x_25, 4);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_55 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
x_56 = lean_ctor_get(x_26, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_26, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_58 = x_26;
} else {
 lean_dec_ref(x_26);
 x_58 = lean_box(0);
}
x_59 = l_Std_PersistentArray_push___rarg(x_57, x_1);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 1);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_55);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_52);
lean_ctor_set(x_61, 3, x_53);
lean_ctor_set(x_61, 4, x_54);
lean_ctor_set(x_61, 5, x_60);
x_62 = lean_st_ref_set(x_3, x_61, x_27);
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
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected unexpanded structure field");
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_28 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_26, x_27, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_26);
x_15 = x_28;
goto block_23;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_24);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 2);
x_40 = lean_ctor_get(x_13, 3);
lean_dec(x_40);
x_41 = lean_ctor_get(x_13, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 1);
lean_inc(x_43);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Meta_whnfForall(x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 7)
{
switch (lean_obj_tag(x_39)) {
case 0:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_47);
x_51 = lean_box(0);
x_52 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_53 = l_Lean_Elab_Term_elabTermEnsuringType(x_49, x_50, x_52, x_51, x_4, x_5, x_6, x_7, x_8, x_9, x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_54);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_54);
lean_ctor_set(x_57, 3, x_42);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_Std_PersistentArray_empty___closed__1;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_inc(x_54);
x_64 = l_Lean_mkApp(x_32, x_54);
x_65 = lean_expr_instantiate1(x_48, x_54);
lean_dec(x_48);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_13, 3, x_66);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_65);
lean_ctor_set(x_2, 0, x_64);
lean_ctor_set(x_61, 0, x_2);
x_15 = x_61;
goto block_23;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
lean_inc(x_54);
x_68 = l_Lean_mkApp(x_32, x_54);
x_69 = lean_expr_instantiate1(x_48, x_54);
lean_dec(x_48);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_13, 3, x_70);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_69);
lean_ctor_set(x_2, 0, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_67);
x_15 = x_71;
goto block_23;
}
}
else
{
uint8_t x_72; 
lean_dec(x_48);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_72 = !lean_is_exclusive(x_53);
if (x_72 == 0)
{
x_15 = x_53;
goto block_23;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_53, 0);
x_74 = lean_ctor_get(x_53, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_53);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_15 = x_75;
goto block_23;
}
}
}
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_dec(x_44);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
lean_dec(x_45);
x_79 = !lean_is_exclusive(x_39);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_39, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_77);
x_81 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_80, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_free_object(x_2);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_77);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_84);
x_85 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_80, x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
x_91 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_92 = l_Lean_Elab_Term_ensureHasType(x_84, x_89, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_ctor_set(x_39, 0, x_90);
x_95 = lean_ctor_get(x_6, 1);
lean_inc(x_95);
lean_inc(x_93);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_43);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_42);
x_97 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = l_Std_PersistentArray_empty___closed__1;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_99, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
lean_inc(x_93);
x_103 = l_Lean_mkApp(x_32, x_93);
x_104 = lean_expr_instantiate1(x_78, x_93);
lean_dec(x_78);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_13, 3, x_105);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 0, x_104);
lean_ctor_set(x_24, 1, x_86);
lean_ctor_set(x_24, 0, x_103);
lean_ctor_set(x_100, 0, x_24);
x_15 = x_100;
goto block_23;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec(x_100);
lean_inc(x_93);
x_107 = l_Lean_mkApp(x_32, x_93);
x_108 = lean_expr_instantiate1(x_78, x_93);
lean_dec(x_78);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_93);
lean_ctor_set(x_13, 3, x_109);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_86, 1, x_3);
lean_ctor_set(x_86, 0, x_108);
lean_ctor_set(x_24, 1, x_86);
lean_ctor_set(x_24, 0, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_24);
lean_ctor_set(x_110, 1, x_106);
x_15 = x_110;
goto block_23;
}
}
else
{
uint8_t x_111; 
lean_free_object(x_86);
lean_dec(x_90);
lean_free_object(x_39);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_111 = !lean_is_exclusive(x_92);
if (x_111 == 0)
{
x_15 = x_92;
goto block_23;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_92, 0);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_92);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_15 = x_114;
goto block_23;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_86, 0);
x_116 = lean_ctor_get(x_86, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_86);
x_117 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_118 = l_Lean_Elab_Term_ensureHasType(x_84, x_115, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_ctor_set(x_39, 0, x_116);
x_121 = lean_ctor_get(x_6, 1);
lean_inc(x_121);
lean_inc(x_119);
x_122 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_122, 0, x_43);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set(x_122, 2, x_119);
lean_ctor_set(x_122, 3, x_42);
x_123 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = l_Std_PersistentArray_empty___closed__1;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_125, x_4, x_5, x_6, x_7, x_8, x_9, x_120);
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_128 = x_126;
} else {
 lean_dec_ref(x_126);
 x_128 = lean_box(0);
}
lean_inc(x_119);
x_129 = l_Lean_mkApp(x_32, x_119);
x_130 = lean_expr_instantiate1(x_78, x_119);
lean_dec(x_78);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_119);
lean_ctor_set(x_13, 3, x_131);
lean_ctor_set(x_3, 1, x_37);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_3);
lean_ctor_set(x_24, 1, x_132);
lean_ctor_set(x_24, 0, x_129);
if (lean_is_scalar(x_128)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_128;
}
lean_ctor_set(x_133, 0, x_24);
lean_ctor_set(x_133, 1, x_127);
x_15 = x_133;
goto block_23;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_116);
lean_free_object(x_39);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_134 = lean_ctor_get(x_118, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_118, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_136 = x_118;
} else {
 lean_dec_ref(x_118);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
x_15 = x_137;
goto block_23;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_84);
lean_free_object(x_39);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_138 = !lean_is_exclusive(x_85);
if (x_138 == 0)
{
x_15 = x_85;
goto block_23;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_85, 0);
x_140 = lean_ctor_get(x_85, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_85);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_15 = x_141;
goto block_23;
}
}
}
else
{
lean_object* x_142; uint8_t x_143; 
lean_dec(x_80);
lean_dec(x_77);
x_142 = lean_ctor_get(x_81, 1);
lean_inc(x_142);
lean_dec(x_81);
x_143 = !lean_is_exclusive(x_82);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_144 = lean_ctor_get(x_82, 0);
x_145 = l_Lean_mkHole(x_38);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_145);
x_146 = lean_ctor_get(x_6, 1);
lean_inc(x_146);
lean_inc(x_144);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_43);
lean_ctor_set(x_147, 1, x_146);
lean_ctor_set(x_147, 2, x_144);
lean_ctor_set(x_147, 3, x_42);
x_148 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = l_Std_PersistentArray_empty___closed__1;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_150, x_4, x_5, x_6, x_7, x_8, x_9, x_142);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_151, 0);
lean_dec(x_153);
lean_inc(x_144);
x_154 = l_Lean_mkApp(x_32, x_144);
x_155 = lean_expr_instantiate1(x_78, x_144);
lean_dec(x_78);
lean_ctor_set(x_13, 3, x_82);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_155);
lean_ctor_set(x_2, 0, x_154);
lean_ctor_set(x_151, 0, x_2);
x_15 = x_151;
goto block_23;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
lean_dec(x_151);
lean_inc(x_144);
x_157 = l_Lean_mkApp(x_32, x_144);
x_158 = lean_expr_instantiate1(x_78, x_144);
lean_dec(x_78);
lean_ctor_set(x_13, 3, x_82);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_158);
lean_ctor_set(x_2, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_2);
lean_ctor_set(x_159, 1, x_156);
x_15 = x_159;
goto block_23;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_160 = lean_ctor_get(x_82, 0);
lean_inc(x_160);
lean_dec(x_82);
x_161 = l_Lean_mkHole(x_38);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_161);
x_162 = lean_ctor_get(x_6, 1);
lean_inc(x_162);
lean_inc(x_160);
x_163 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_163, 0, x_43);
lean_ctor_set(x_163, 1, x_162);
lean_ctor_set(x_163, 2, x_160);
lean_ctor_set(x_163, 3, x_42);
x_164 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = l_Std_PersistentArray_empty___closed__1;
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_166, x_4, x_5, x_6, x_7, x_8, x_9, x_142);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
lean_inc(x_160);
x_170 = l_Lean_mkApp(x_32, x_160);
x_171 = lean_expr_instantiate1(x_78, x_160);
lean_dec(x_78);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_160);
lean_ctor_set(x_13, 3, x_172);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_171);
lean_ctor_set(x_2, 0, x_170);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_168);
x_15 = x_173;
goto block_23;
}
}
}
else
{
uint8_t x_174; 
lean_free_object(x_39);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_174 = !lean_is_exclusive(x_81);
if (x_174 == 0)
{
x_15 = x_81;
goto block_23;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_81, 0);
x_176 = lean_ctor_get(x_81, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_81);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_15 = x_177;
goto block_23;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_39, 0);
lean_inc(x_178);
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_77);
x_179 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_178, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_free_object(x_2);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_77);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_182);
x_183 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_178, x_182, x_4, x_5, x_6, x_7, x_8, x_9, x_181);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_190 = l_Lean_Elab_Term_ensureHasType(x_182, x_186, x_189, x_4, x_5, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_187);
x_194 = lean_ctor_get(x_6, 1);
lean_inc(x_194);
lean_inc(x_191);
x_195 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_195, 0, x_43);
lean_ctor_set(x_195, 1, x_194);
lean_ctor_set(x_195, 2, x_191);
lean_ctor_set(x_195, 3, x_42);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l_Std_PersistentArray_empty___closed__1;
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_198, x_4, x_5, x_6, x_7, x_8, x_9, x_192);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
lean_inc(x_191);
x_202 = l_Lean_mkApp(x_32, x_191);
x_203 = lean_expr_instantiate1(x_78, x_191);
lean_dec(x_78);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_191);
lean_ctor_set(x_13, 3, x_204);
lean_ctor_set(x_13, 2, x_193);
lean_ctor_set(x_3, 1, x_37);
if (lean_is_scalar(x_188)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_188;
}
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_3);
lean_ctor_set(x_24, 1, x_205);
lean_ctor_set(x_24, 0, x_202);
if (lean_is_scalar(x_201)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_201;
}
lean_ctor_set(x_206, 0, x_24);
lean_ctor_set(x_206, 1, x_200);
x_15 = x_206;
goto block_23;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_207 = lean_ctor_get(x_190, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_190, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_209 = x_190;
} else {
 lean_dec_ref(x_190);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
x_15 = x_210;
goto block_23;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_182);
lean_dec(x_78);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_211 = lean_ctor_get(x_183, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_183, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_213 = x_183;
} else {
 lean_dec_ref(x_183);
 x_213 = lean_box(0);
}
if (lean_is_scalar(x_213)) {
 x_214 = lean_alloc_ctor(1, 2, 0);
} else {
 x_214 = x_213;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_212);
x_15 = x_214;
goto block_23;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
lean_dec(x_178);
lean_dec(x_77);
x_215 = lean_ctor_get(x_179, 1);
lean_inc(x_215);
lean_dec(x_179);
x_216 = lean_ctor_get(x_180, 0);
lean_inc(x_216);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 x_217 = x_180;
} else {
 lean_dec_ref(x_180);
 x_217 = lean_box(0);
}
x_218 = l_Lean_mkHole(x_38);
x_219 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_219, 0, x_218);
x_220 = lean_ctor_get(x_6, 1);
lean_inc(x_220);
lean_inc(x_216);
x_221 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_221, 0, x_43);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_221, 2, x_216);
lean_ctor_set(x_221, 3, x_42);
x_222 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = l_Std_PersistentArray_empty___closed__1;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_224, x_4, x_5, x_6, x_7, x_8, x_9, x_215);
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
lean_inc(x_216);
x_228 = l_Lean_mkApp(x_32, x_216);
x_229 = lean_expr_instantiate1(x_78, x_216);
lean_dec(x_78);
if (lean_is_scalar(x_217)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_217;
}
lean_ctor_set(x_230, 0, x_216);
lean_ctor_set(x_13, 3, x_230);
lean_ctor_set(x_13, 2, x_219);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_229);
lean_ctor_set(x_2, 0, x_228);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_231 = x_227;
}
lean_ctor_set(x_231, 0, x_2);
lean_ctor_set(x_231, 1, x_226);
x_15 = x_231;
goto block_23;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_178);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_232 = lean_ctor_get(x_179, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_179, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_234 = x_179;
} else {
 lean_dec_ref(x_179);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
x_15 = x_235;
goto block_23;
}
}
}
default: 
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_236 = lean_ctor_get(x_44, 1);
lean_inc(x_236);
lean_dec(x_44);
x_237 = lean_ctor_get(x_45, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_45, 2);
lean_inc(x_238);
lean_dec(x_45);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_237);
x_240 = lean_ctor_get(x_8, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_8, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_8, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_8, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_8, 4);
lean_inc(x_244);
x_245 = lean_ctor_get(x_8, 5);
lean_inc(x_245);
x_246 = l_Lean_replaceRef(x_38, x_243);
lean_dec(x_243);
x_247 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_241);
lean_ctor_set(x_247, 2, x_242);
lean_ctor_set(x_247, 3, x_246);
lean_ctor_set(x_247, 4, x_244);
lean_ctor_set(x_247, 5, x_245);
x_248 = 0;
x_249 = lean_box(0);
lean_inc(x_6);
x_250 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_239, x_248, x_249, x_6, x_7, x_247, x_9, x_236);
lean_dec(x_247);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_251);
x_254 = lean_ctor_get(x_6, 1);
lean_inc(x_254);
lean_inc(x_253);
x_255 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_255, 0, x_43);
lean_ctor_set(x_255, 1, x_254);
lean_ctor_set(x_255, 2, x_253);
lean_ctor_set(x_255, 3, x_42);
x_256 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_256, 0, x_255);
x_257 = l_Std_PersistentArray_empty___closed__1;
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_258, x_4, x_5, x_6, x_7, x_8, x_9, x_252);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_259, 0);
lean_dec(x_261);
lean_inc(x_253);
x_262 = l_Lean_mkApp(x_32, x_253);
x_263 = lean_expr_instantiate1(x_238, x_253);
lean_dec(x_238);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_253);
lean_ctor_set(x_13, 3, x_264);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_263);
lean_ctor_set(x_2, 0, x_262);
lean_ctor_set(x_259, 0, x_2);
x_15 = x_259;
goto block_23;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_259, 1);
lean_inc(x_265);
lean_dec(x_259);
lean_inc(x_253);
x_266 = l_Lean_mkApp(x_32, x_253);
x_267 = lean_expr_instantiate1(x_238, x_253);
lean_dec(x_238);
x_268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_268, 0, x_253);
lean_ctor_set(x_13, 3, x_268);
lean_ctor_set(x_3, 1, x_37);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_267);
lean_ctor_set(x_2, 0, x_266);
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_2);
lean_ctor_set(x_269, 1, x_265);
x_15 = x_269;
goto block_23;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_39);
lean_free_object(x_24);
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_270 = lean_ctor_get(x_44, 1);
lean_inc(x_270);
lean_dec(x_44);
x_271 = l_Lean_indentExpr(x_45);
x_272 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
x_273 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_Lean_KernelException_toMessageData___closed__15;
x_275 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_ctor_get(x_8, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_8, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_8, 2);
lean_inc(x_278);
x_279 = lean_ctor_get(x_8, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_8, 4);
lean_inc(x_280);
x_281 = lean_ctor_get(x_8, 5);
lean_inc(x_281);
x_282 = l_Lean_replaceRef(x_38, x_279);
lean_dec(x_279);
lean_dec(x_38);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_276);
lean_ctor_set(x_283, 1, x_277);
lean_ctor_set(x_283, 2, x_278);
lean_ctor_set(x_283, 3, x_282);
lean_ctor_set(x_283, 4, x_280);
lean_ctor_set(x_283, 5, x_281);
lean_inc(x_4);
lean_inc(x_1);
x_284 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_43, x_1, x_275, x_4, x_5, x_6, x_7, x_283, x_9, x_270);
lean_dec(x_283);
x_15 = x_284;
goto block_23;
}
}
else
{
uint8_t x_285; 
lean_dec(x_43);
lean_dec(x_42);
lean_free_object(x_13);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_24);
lean_dec(x_37);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_285 = !lean_is_exclusive(x_44);
if (x_285 == 0)
{
x_15 = x_44;
goto block_23;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_44, 0);
x_287 = lean_ctor_get(x_44, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_44);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_15 = x_288;
goto block_23;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_24, 0);
x_290 = lean_ctor_get(x_24, 1);
x_291 = lean_ctor_get(x_13, 0);
x_292 = lean_ctor_get(x_13, 2);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_13);
x_293 = lean_ctor_get(x_29, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_29, 1);
lean_inc(x_294);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_295 = l_Lean_Meta_whnfForall(x_289, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 7)
{
switch (lean_obj_tag(x_292)) {
case 0:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 2);
lean_inc(x_299);
lean_dec(x_296);
x_300 = lean_ctor_get(x_292, 0);
lean_inc(x_300);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_298);
x_302 = lean_box(0);
x_303 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_304 = l_Lean_Elab_Term_elabTermEnsuringType(x_300, x_301, x_303, x_302, x_4, x_5, x_6, x_7, x_8, x_9, x_297);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_ctor_get(x_6, 1);
lean_inc(x_307);
lean_inc(x_305);
x_308 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_308, 0, x_294);
lean_ctor_set(x_308, 1, x_307);
lean_ctor_set(x_308, 2, x_305);
lean_ctor_set(x_308, 3, x_293);
x_309 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = l_Std_PersistentArray_empty___closed__1;
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_311, x_4, x_5, x_6, x_7, x_8, x_9, x_306);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 x_314 = x_312;
} else {
 lean_dec_ref(x_312);
 x_314 = lean_box(0);
}
lean_inc(x_305);
x_315 = l_Lean_mkApp(x_32, x_305);
x_316 = lean_expr_instantiate1(x_299, x_305);
lean_dec(x_299);
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_305);
x_318 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_318, 0, x_291);
lean_ctor_set(x_318, 1, x_25);
lean_ctor_set(x_318, 2, x_292);
lean_ctor_set(x_318, 3, x_317);
lean_ctor_set(x_3, 1, x_290);
lean_ctor_set(x_3, 0, x_318);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_316);
lean_ctor_set(x_2, 0, x_315);
if (lean_is_scalar(x_314)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_314;
}
lean_ctor_set(x_319, 0, x_2);
lean_ctor_set(x_319, 1, x_313);
x_15 = x_319;
goto block_23;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_299);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_free_object(x_24);
lean_dec(x_290);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_320 = lean_ctor_get(x_304, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_304, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_322 = x_304;
} else {
 lean_dec_ref(x_304);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
x_15 = x_323;
goto block_23;
}
}
case 1:
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_295, 1);
lean_inc(x_324);
lean_dec(x_295);
x_325 = lean_ctor_get(x_296, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_296, 2);
lean_inc(x_326);
lean_dec(x_296);
x_327 = lean_ctor_get(x_292, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_328 = x_292;
} else {
 lean_dec_ref(x_292);
 x_328 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_325);
x_329 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_327, x_325, x_4, x_5, x_6, x_7, x_8, x_9, x_324);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_free_object(x_2);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_332, 0, x_325);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_332);
x_333 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_327, x_332, x_4, x_5, x_6, x_7, x_8, x_9, x_331);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
x_336 = lean_ctor_get(x_334, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_334, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_334)) {
 lean_ctor_release(x_334, 0);
 lean_ctor_release(x_334, 1);
 x_338 = x_334;
} else {
 lean_dec_ref(x_334);
 x_338 = lean_box(0);
}
x_339 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_340 = l_Lean_Elab_Term_ensureHasType(x_332, x_336, x_339, x_4, x_5, x_6, x_7, x_8, x_9, x_335);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
if (lean_is_scalar(x_328)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_328;
}
lean_ctor_set(x_343, 0, x_337);
x_344 = lean_ctor_get(x_6, 1);
lean_inc(x_344);
lean_inc(x_341);
x_345 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_345, 0, x_294);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set(x_345, 2, x_341);
lean_ctor_set(x_345, 3, x_293);
x_346 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_346, 0, x_345);
x_347 = l_Std_PersistentArray_empty___closed__1;
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_348, x_4, x_5, x_6, x_7, x_8, x_9, x_342);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_351 = x_349;
} else {
 lean_dec_ref(x_349);
 x_351 = lean_box(0);
}
lean_inc(x_341);
x_352 = l_Lean_mkApp(x_32, x_341);
x_353 = lean_expr_instantiate1(x_326, x_341);
lean_dec(x_326);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_341);
x_355 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_355, 0, x_291);
lean_ctor_set(x_355, 1, x_25);
lean_ctor_set(x_355, 2, x_343);
lean_ctor_set(x_355, 3, x_354);
lean_ctor_set(x_3, 1, x_290);
lean_ctor_set(x_3, 0, x_355);
if (lean_is_scalar(x_338)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_338;
}
lean_ctor_set(x_356, 0, x_353);
lean_ctor_set(x_356, 1, x_3);
lean_ctor_set(x_24, 1, x_356);
lean_ctor_set(x_24, 0, x_352);
if (lean_is_scalar(x_351)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_351;
}
lean_ctor_set(x_357, 0, x_24);
lean_ctor_set(x_357, 1, x_350);
x_15 = x_357;
goto block_23;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_291);
lean_free_object(x_24);
lean_dec(x_290);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_358 = lean_ctor_get(x_340, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_340, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_360 = x_340;
} else {
 lean_dec_ref(x_340);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
x_15 = x_361;
goto block_23;
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_332);
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_291);
lean_free_object(x_24);
lean_dec(x_290);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_362 = lean_ctor_get(x_333, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_333, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_364 = x_333;
} else {
 lean_dec_ref(x_333);
 x_364 = lean_box(0);
}
if (lean_is_scalar(x_364)) {
 x_365 = lean_alloc_ctor(1, 2, 0);
} else {
 x_365 = x_364;
}
lean_ctor_set(x_365, 0, x_362);
lean_ctor_set(x_365, 1, x_363);
x_15 = x_365;
goto block_23;
}
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_327);
lean_dec(x_325);
x_366 = lean_ctor_get(x_329, 1);
lean_inc(x_366);
lean_dec(x_329);
x_367 = lean_ctor_get(x_330, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_368 = x_330;
} else {
 lean_dec_ref(x_330);
 x_368 = lean_box(0);
}
x_369 = l_Lean_mkHole(x_291);
if (lean_is_scalar(x_328)) {
 x_370 = lean_alloc_ctor(0, 1, 0);
} else {
 x_370 = x_328;
 lean_ctor_set_tag(x_370, 0);
}
lean_ctor_set(x_370, 0, x_369);
x_371 = lean_ctor_get(x_6, 1);
lean_inc(x_371);
lean_inc(x_367);
x_372 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_372, 0, x_294);
lean_ctor_set(x_372, 1, x_371);
lean_ctor_set(x_372, 2, x_367);
lean_ctor_set(x_372, 3, x_293);
x_373 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_373, 0, x_372);
x_374 = l_Std_PersistentArray_empty___closed__1;
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_375, x_4, x_5, x_6, x_7, x_8, x_9, x_366);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
lean_inc(x_367);
x_379 = l_Lean_mkApp(x_32, x_367);
x_380 = lean_expr_instantiate1(x_326, x_367);
lean_dec(x_326);
if (lean_is_scalar(x_368)) {
 x_381 = lean_alloc_ctor(1, 1, 0);
} else {
 x_381 = x_368;
}
lean_ctor_set(x_381, 0, x_367);
x_382 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_382, 0, x_291);
lean_ctor_set(x_382, 1, x_25);
lean_ctor_set(x_382, 2, x_370);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set(x_3, 1, x_290);
lean_ctor_set(x_3, 0, x_382);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_380);
lean_ctor_set(x_2, 0, x_379);
if (lean_is_scalar(x_378)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_378;
}
lean_ctor_set(x_383, 0, x_2);
lean_ctor_set(x_383, 1, x_377);
x_15 = x_383;
goto block_23;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_328);
lean_dec(x_327);
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_291);
lean_free_object(x_24);
lean_dec(x_290);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_384 = lean_ctor_get(x_329, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_329, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_386 = x_329;
} else {
 lean_dec_ref(x_329);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
x_15 = x_387;
goto block_23;
}
}
default: 
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_388 = lean_ctor_get(x_295, 1);
lean_inc(x_388);
lean_dec(x_295);
x_389 = lean_ctor_get(x_296, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_296, 2);
lean_inc(x_390);
lean_dec(x_296);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_392 = lean_ctor_get(x_8, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_8, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_8, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_8, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_8, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_8, 5);
lean_inc(x_397);
x_398 = l_Lean_replaceRef(x_291, x_395);
lean_dec(x_395);
x_399 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_399, 0, x_392);
lean_ctor_set(x_399, 1, x_393);
lean_ctor_set(x_399, 2, x_394);
lean_ctor_set(x_399, 3, x_398);
lean_ctor_set(x_399, 4, x_396);
lean_ctor_set(x_399, 5, x_397);
x_400 = 0;
x_401 = lean_box(0);
lean_inc(x_6);
x_402 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_391, x_400, x_401, x_6, x_7, x_399, x_9, x_388);
lean_dec(x_399);
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_403);
x_406 = lean_ctor_get(x_6, 1);
lean_inc(x_406);
lean_inc(x_405);
x_407 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_407, 0, x_294);
lean_ctor_set(x_407, 1, x_406);
lean_ctor_set(x_407, 2, x_405);
lean_ctor_set(x_407, 3, x_293);
x_408 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_408, 0, x_407);
x_409 = l_Std_PersistentArray_empty___closed__1;
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
x_411 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_410, x_4, x_5, x_6, x_7, x_8, x_9, x_404);
x_412 = lean_ctor_get(x_411, 1);
lean_inc(x_412);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_413 = x_411;
} else {
 lean_dec_ref(x_411);
 x_413 = lean_box(0);
}
lean_inc(x_405);
x_414 = l_Lean_mkApp(x_32, x_405);
x_415 = lean_expr_instantiate1(x_390, x_405);
lean_dec(x_390);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_405);
x_417 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_417, 0, x_291);
lean_ctor_set(x_417, 1, x_25);
lean_ctor_set(x_417, 2, x_292);
lean_ctor_set(x_417, 3, x_416);
lean_ctor_set(x_3, 1, x_290);
lean_ctor_set(x_3, 0, x_417);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_415);
lean_ctor_set(x_2, 0, x_414);
if (lean_is_scalar(x_413)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_413;
}
lean_ctor_set(x_418, 0, x_2);
lean_ctor_set(x_418, 1, x_412);
x_15 = x_418;
goto block_23;
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_293);
lean_dec(x_292);
lean_free_object(x_24);
lean_dec(x_290);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_419 = lean_ctor_get(x_295, 1);
lean_inc(x_419);
lean_dec(x_295);
x_420 = l_Lean_indentExpr(x_296);
x_421 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
x_422 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
x_423 = l_Lean_KernelException_toMessageData___closed__15;
x_424 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_423);
x_425 = lean_ctor_get(x_8, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_8, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_8, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_8, 3);
lean_inc(x_428);
x_429 = lean_ctor_get(x_8, 4);
lean_inc(x_429);
x_430 = lean_ctor_get(x_8, 5);
lean_inc(x_430);
x_431 = l_Lean_replaceRef(x_291, x_428);
lean_dec(x_428);
lean_dec(x_291);
x_432 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_432, 0, x_425);
lean_ctor_set(x_432, 1, x_426);
lean_ctor_set(x_432, 2, x_427);
lean_ctor_set(x_432, 3, x_431);
lean_ctor_set(x_432, 4, x_429);
lean_ctor_set(x_432, 5, x_430);
lean_inc(x_4);
lean_inc(x_1);
x_433 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_294, x_1, x_424, x_4, x_5, x_6, x_7, x_432, x_9, x_419);
lean_dec(x_432);
x_15 = x_433;
goto block_23;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_291);
lean_free_object(x_24);
lean_dec(x_290);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_434 = lean_ctor_get(x_295, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_295, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_436 = x_295;
} else {
 lean_dec_ref(x_295);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
x_15 = x_437;
goto block_23;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_438 = lean_ctor_get(x_24, 0);
x_439 = lean_ctor_get(x_24, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_24);
x_440 = lean_ctor_get(x_13, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_13, 2);
lean_inc(x_441);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_442 = x_13;
} else {
 lean_dec_ref(x_13);
 x_442 = lean_box(0);
}
x_443 = lean_ctor_get(x_29, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_29, 1);
lean_inc(x_444);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_445 = l_Lean_Meta_whnfForall(x_438, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
if (lean_obj_tag(x_446) == 7)
{
switch (lean_obj_tag(x_441)) {
case 0:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; 
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_446, 2);
lean_inc(x_449);
lean_dec(x_446);
x_450 = lean_ctor_get(x_441, 0);
lean_inc(x_450);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_448);
x_452 = lean_box(0);
x_453 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_454 = l_Lean_Elab_Term_elabTermEnsuringType(x_450, x_451, x_453, x_452, x_4, x_5, x_6, x_7, x_8, x_9, x_447);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_454, 1);
lean_inc(x_456);
lean_dec(x_454);
x_457 = lean_ctor_get(x_6, 1);
lean_inc(x_457);
lean_inc(x_455);
x_458 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_458, 0, x_444);
lean_ctor_set(x_458, 1, x_457);
lean_ctor_set(x_458, 2, x_455);
lean_ctor_set(x_458, 3, x_443);
x_459 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_459, 0, x_458);
x_460 = l_Std_PersistentArray_empty___closed__1;
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
x_462 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_461, x_4, x_5, x_6, x_7, x_8, x_9, x_456);
x_463 = lean_ctor_get(x_462, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_464 = x_462;
} else {
 lean_dec_ref(x_462);
 x_464 = lean_box(0);
}
lean_inc(x_455);
x_465 = l_Lean_mkApp(x_32, x_455);
x_466 = lean_expr_instantiate1(x_449, x_455);
lean_dec(x_449);
x_467 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_467, 0, x_455);
if (lean_is_scalar(x_442)) {
 x_468 = lean_alloc_ctor(0, 4, 0);
} else {
 x_468 = x_442;
}
lean_ctor_set(x_468, 0, x_440);
lean_ctor_set(x_468, 1, x_25);
lean_ctor_set(x_468, 2, x_441);
lean_ctor_set(x_468, 3, x_467);
lean_ctor_set(x_3, 1, x_439);
lean_ctor_set(x_3, 0, x_468);
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_3);
lean_ctor_set(x_2, 1, x_469);
lean_ctor_set(x_2, 0, x_465);
if (lean_is_scalar(x_464)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_464;
}
lean_ctor_set(x_470, 0, x_2);
lean_ctor_set(x_470, 1, x_463);
x_15 = x_470;
goto block_23;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_449);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_471 = lean_ctor_get(x_454, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_454, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_473 = x_454;
} else {
 lean_dec_ref(x_454);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_471);
lean_ctor_set(x_474, 1, x_472);
x_15 = x_474;
goto block_23;
}
}
case 1:
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_475 = lean_ctor_get(x_445, 1);
lean_inc(x_475);
lean_dec(x_445);
x_476 = lean_ctor_get(x_446, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_446, 2);
lean_inc(x_477);
lean_dec(x_446);
x_478 = lean_ctor_get(x_441, 0);
lean_inc(x_478);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 x_479 = x_441;
} else {
 lean_dec_ref(x_441);
 x_479 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_476);
x_480 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_478, x_476, x_4, x_5, x_6, x_7, x_8, x_9, x_475);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_free_object(x_2);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_483, 0, x_476);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_483);
x_484 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_478, x_483, x_4, x_5, x_6, x_7, x_8, x_9, x_482);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_485, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 lean_ctor_release(x_485, 1);
 x_489 = x_485;
} else {
 lean_dec_ref(x_485);
 x_489 = lean_box(0);
}
x_490 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_491 = l_Lean_Elab_Term_ensureHasType(x_483, x_487, x_490, x_4, x_5, x_6, x_7, x_8, x_9, x_486);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
if (lean_is_scalar(x_479)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_479;
}
lean_ctor_set(x_494, 0, x_488);
x_495 = lean_ctor_get(x_6, 1);
lean_inc(x_495);
lean_inc(x_492);
x_496 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_496, 0, x_444);
lean_ctor_set(x_496, 1, x_495);
lean_ctor_set(x_496, 2, x_492);
lean_ctor_set(x_496, 3, x_443);
x_497 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = l_Std_PersistentArray_empty___closed__1;
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_500 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_499, x_4, x_5, x_6, x_7, x_8, x_9, x_493);
x_501 = lean_ctor_get(x_500, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_502 = x_500;
} else {
 lean_dec_ref(x_500);
 x_502 = lean_box(0);
}
lean_inc(x_492);
x_503 = l_Lean_mkApp(x_32, x_492);
x_504 = lean_expr_instantiate1(x_477, x_492);
lean_dec(x_477);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_492);
if (lean_is_scalar(x_442)) {
 x_506 = lean_alloc_ctor(0, 4, 0);
} else {
 x_506 = x_442;
}
lean_ctor_set(x_506, 0, x_440);
lean_ctor_set(x_506, 1, x_25);
lean_ctor_set(x_506, 2, x_494);
lean_ctor_set(x_506, 3, x_505);
lean_ctor_set(x_3, 1, x_439);
lean_ctor_set(x_3, 0, x_506);
if (lean_is_scalar(x_489)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_489;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_3);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_503);
lean_ctor_set(x_508, 1, x_507);
if (lean_is_scalar(x_502)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_502;
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_501);
x_15 = x_509;
goto block_23;
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_510 = lean_ctor_get(x_491, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_491, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_512 = x_491;
} else {
 lean_dec_ref(x_491);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_511);
x_15 = x_513;
goto block_23;
}
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
lean_dec(x_483);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_514 = lean_ctor_get(x_484, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_484, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_516 = x_484;
} else {
 lean_dec_ref(x_484);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_516;
}
lean_ctor_set(x_517, 0, x_514);
lean_ctor_set(x_517, 1, x_515);
x_15 = x_517;
goto block_23;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_dec(x_478);
lean_dec(x_476);
x_518 = lean_ctor_get(x_480, 1);
lean_inc(x_518);
lean_dec(x_480);
x_519 = lean_ctor_get(x_481, 0);
lean_inc(x_519);
if (lean_is_exclusive(x_481)) {
 lean_ctor_release(x_481, 0);
 x_520 = x_481;
} else {
 lean_dec_ref(x_481);
 x_520 = lean_box(0);
}
x_521 = l_Lean_mkHole(x_440);
if (lean_is_scalar(x_479)) {
 x_522 = lean_alloc_ctor(0, 1, 0);
} else {
 x_522 = x_479;
 lean_ctor_set_tag(x_522, 0);
}
lean_ctor_set(x_522, 0, x_521);
x_523 = lean_ctor_get(x_6, 1);
lean_inc(x_523);
lean_inc(x_519);
x_524 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_524, 0, x_444);
lean_ctor_set(x_524, 1, x_523);
lean_ctor_set(x_524, 2, x_519);
lean_ctor_set(x_524, 3, x_443);
x_525 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_525, 0, x_524);
x_526 = l_Std_PersistentArray_empty___closed__1;
x_527 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
x_528 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_527, x_4, x_5, x_6, x_7, x_8, x_9, x_518);
x_529 = lean_ctor_get(x_528, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_530 = x_528;
} else {
 lean_dec_ref(x_528);
 x_530 = lean_box(0);
}
lean_inc(x_519);
x_531 = l_Lean_mkApp(x_32, x_519);
x_532 = lean_expr_instantiate1(x_477, x_519);
lean_dec(x_477);
if (lean_is_scalar(x_520)) {
 x_533 = lean_alloc_ctor(1, 1, 0);
} else {
 x_533 = x_520;
}
lean_ctor_set(x_533, 0, x_519);
if (lean_is_scalar(x_442)) {
 x_534 = lean_alloc_ctor(0, 4, 0);
} else {
 x_534 = x_442;
}
lean_ctor_set(x_534, 0, x_440);
lean_ctor_set(x_534, 1, x_25);
lean_ctor_set(x_534, 2, x_522);
lean_ctor_set(x_534, 3, x_533);
lean_ctor_set(x_3, 1, x_439);
lean_ctor_set(x_3, 0, x_534);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_532);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_2, 1, x_535);
lean_ctor_set(x_2, 0, x_531);
if (lean_is_scalar(x_530)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_530;
}
lean_ctor_set(x_536, 0, x_2);
lean_ctor_set(x_536, 1, x_529);
x_15 = x_536;
goto block_23;
}
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_479);
lean_dec(x_478);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_440);
lean_dec(x_439);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_537 = lean_ctor_get(x_480, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_480, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_480)) {
 lean_ctor_release(x_480, 0);
 lean_ctor_release(x_480, 1);
 x_539 = x_480;
} else {
 lean_dec_ref(x_480);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
x_15 = x_540;
goto block_23;
}
}
default: 
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; uint8_t x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_541 = lean_ctor_get(x_445, 1);
lean_inc(x_541);
lean_dec(x_445);
x_542 = lean_ctor_get(x_446, 1);
lean_inc(x_542);
x_543 = lean_ctor_get(x_446, 2);
lean_inc(x_543);
lean_dec(x_446);
x_544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_544, 0, x_542);
x_545 = lean_ctor_get(x_8, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_8, 1);
lean_inc(x_546);
x_547 = lean_ctor_get(x_8, 2);
lean_inc(x_547);
x_548 = lean_ctor_get(x_8, 3);
lean_inc(x_548);
x_549 = lean_ctor_get(x_8, 4);
lean_inc(x_549);
x_550 = lean_ctor_get(x_8, 5);
lean_inc(x_550);
x_551 = l_Lean_replaceRef(x_440, x_548);
lean_dec(x_548);
x_552 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_552, 0, x_545);
lean_ctor_set(x_552, 1, x_546);
lean_ctor_set(x_552, 2, x_547);
lean_ctor_set(x_552, 3, x_551);
lean_ctor_set(x_552, 4, x_549);
lean_ctor_set(x_552, 5, x_550);
x_553 = 0;
x_554 = lean_box(0);
lean_inc(x_6);
x_555 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_544, x_553, x_554, x_6, x_7, x_552, x_9, x_541);
lean_dec(x_552);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_556);
x_559 = lean_ctor_get(x_6, 1);
lean_inc(x_559);
lean_inc(x_558);
x_560 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_560, 0, x_444);
lean_ctor_set(x_560, 1, x_559);
lean_ctor_set(x_560, 2, x_558);
lean_ctor_set(x_560, 3, x_443);
x_561 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_561, 0, x_560);
x_562 = l_Std_PersistentArray_empty___closed__1;
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_563, x_4, x_5, x_6, x_7, x_8, x_9, x_557);
x_565 = lean_ctor_get(x_564, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_566 = x_564;
} else {
 lean_dec_ref(x_564);
 x_566 = lean_box(0);
}
lean_inc(x_558);
x_567 = l_Lean_mkApp(x_32, x_558);
x_568 = lean_expr_instantiate1(x_543, x_558);
lean_dec(x_543);
x_569 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_569, 0, x_558);
if (lean_is_scalar(x_442)) {
 x_570 = lean_alloc_ctor(0, 4, 0);
} else {
 x_570 = x_442;
}
lean_ctor_set(x_570, 0, x_440);
lean_ctor_set(x_570, 1, x_25);
lean_ctor_set(x_570, 2, x_441);
lean_ctor_set(x_570, 3, x_569);
lean_ctor_set(x_3, 1, x_439);
lean_ctor_set(x_3, 0, x_570);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_3);
lean_ctor_set(x_2, 1, x_571);
lean_ctor_set(x_2, 0, x_567);
if (lean_is_scalar(x_566)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_566;
}
lean_ctor_set(x_572, 0, x_2);
lean_ctor_set(x_572, 1, x_565);
x_15 = x_572;
goto block_23;
}
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_439);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_573 = lean_ctor_get(x_445, 1);
lean_inc(x_573);
lean_dec(x_445);
x_574 = l_Lean_indentExpr(x_446);
x_575 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
x_576 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_574);
x_577 = l_Lean_KernelException_toMessageData___closed__15;
x_578 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
x_579 = lean_ctor_get(x_8, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_8, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_8, 2);
lean_inc(x_581);
x_582 = lean_ctor_get(x_8, 3);
lean_inc(x_582);
x_583 = lean_ctor_get(x_8, 4);
lean_inc(x_583);
x_584 = lean_ctor_get(x_8, 5);
lean_inc(x_584);
x_585 = l_Lean_replaceRef(x_440, x_582);
lean_dec(x_582);
lean_dec(x_440);
x_586 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_586, 0, x_579);
lean_ctor_set(x_586, 1, x_580);
lean_ctor_set(x_586, 2, x_581);
lean_ctor_set(x_586, 3, x_585);
lean_ctor_set(x_586, 4, x_583);
lean_ctor_set(x_586, 5, x_584);
lean_inc(x_4);
lean_inc(x_1);
x_587 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_444, x_1, x_578, x_4, x_5, x_6, x_7, x_586, x_9, x_573);
lean_dec(x_586);
x_15 = x_587;
goto block_23;
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
lean_dec(x_444);
lean_dec(x_443);
lean_dec(x_442);
lean_dec(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_free_object(x_2);
lean_dec(x_32);
lean_dec(x_25);
lean_free_object(x_3);
x_588 = lean_ctor_get(x_445, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_445, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_590 = x_445;
} else {
 lean_dec_ref(x_445);
 x_590 = lean_box(0);
}
if (lean_is_scalar(x_590)) {
 x_591 = lean_alloc_ctor(1, 2, 0);
} else {
 x_591 = x_590;
}
lean_ctor_set(x_591, 0, x_588);
lean_ctor_set(x_591, 1, x_589);
x_15 = x_591;
goto block_23;
}
}
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_592 = lean_ctor_get(x_2, 0);
lean_inc(x_592);
lean_dec(x_2);
x_593 = lean_ctor_get(x_24, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_24, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_595 = x_24;
} else {
 lean_dec_ref(x_24);
 x_595 = lean_box(0);
}
x_596 = lean_ctor_get(x_13, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_13, 2);
lean_inc(x_597);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_598 = x_13;
} else {
 lean_dec_ref(x_13);
 x_598 = lean_box(0);
}
x_599 = lean_ctor_get(x_29, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_29, 1);
lean_inc(x_600);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_601 = l_Lean_Meta_whnfForall(x_593, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
if (lean_obj_tag(x_602) == 7)
{
switch (lean_obj_tag(x_597)) {
case 0:
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; lean_object* x_610; 
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
x_605 = lean_ctor_get(x_602, 2);
lean_inc(x_605);
lean_dec(x_602);
x_606 = lean_ctor_get(x_597, 0);
lean_inc(x_606);
x_607 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_607, 0, x_604);
x_608 = lean_box(0);
x_609 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_610 = l_Lean_Elab_Term_elabTermEnsuringType(x_606, x_607, x_609, x_608, x_4, x_5, x_6, x_7, x_8, x_9, x_603);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_ctor_get(x_6, 1);
lean_inc(x_613);
lean_inc(x_611);
x_614 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_614, 0, x_600);
lean_ctor_set(x_614, 1, x_613);
lean_ctor_set(x_614, 2, x_611);
lean_ctor_set(x_614, 3, x_599);
x_615 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_615, 0, x_614);
x_616 = l_Std_PersistentArray_empty___closed__1;
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
x_618 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_617, x_4, x_5, x_6, x_7, x_8, x_9, x_612);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_620 = x_618;
} else {
 lean_dec_ref(x_618);
 x_620 = lean_box(0);
}
lean_inc(x_611);
x_621 = l_Lean_mkApp(x_592, x_611);
x_622 = lean_expr_instantiate1(x_605, x_611);
lean_dec(x_605);
x_623 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_623, 0, x_611);
if (lean_is_scalar(x_598)) {
 x_624 = lean_alloc_ctor(0, 4, 0);
} else {
 x_624 = x_598;
}
lean_ctor_set(x_624, 0, x_596);
lean_ctor_set(x_624, 1, x_25);
lean_ctor_set(x_624, 2, x_597);
lean_ctor_set(x_624, 3, x_623);
lean_ctor_set(x_3, 1, x_594);
lean_ctor_set(x_3, 0, x_624);
if (lean_is_scalar(x_595)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_595;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_3);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_621);
lean_ctor_set(x_626, 1, x_625);
if (lean_is_scalar(x_620)) {
 x_627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_627 = x_620;
}
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_619);
x_15 = x_627;
goto block_23;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_605);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_628 = lean_ctor_get(x_610, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_610, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_630 = x_610;
} else {
 lean_dec_ref(x_610);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
x_15 = x_631;
goto block_23;
}
}
case 1:
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_632 = lean_ctor_get(x_601, 1);
lean_inc(x_632);
lean_dec(x_601);
x_633 = lean_ctor_get(x_602, 1);
lean_inc(x_633);
x_634 = lean_ctor_get(x_602, 2);
lean_inc(x_634);
lean_dec(x_602);
x_635 = lean_ctor_get(x_597, 0);
lean_inc(x_635);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 x_636 = x_597;
} else {
 lean_dec_ref(x_597);
 x_636 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_633);
x_637 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_635, x_633, x_4, x_5, x_6, x_7, x_8, x_9, x_632);
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
x_640 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_640, 0, x_633);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_640);
x_641 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_635, x_640, x_4, x_5, x_6, x_7, x_8, x_9, x_639);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_642, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 lean_ctor_release(x_642, 1);
 x_646 = x_642;
} else {
 lean_dec_ref(x_642);
 x_646 = lean_box(0);
}
x_647 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_648 = l_Lean_Elab_Term_ensureHasType(x_640, x_644, x_647, x_4, x_5, x_6, x_7, x_8, x_9, x_643);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
if (lean_is_scalar(x_636)) {
 x_651 = lean_alloc_ctor(1, 1, 0);
} else {
 x_651 = x_636;
}
lean_ctor_set(x_651, 0, x_645);
x_652 = lean_ctor_get(x_6, 1);
lean_inc(x_652);
lean_inc(x_649);
x_653 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_653, 0, x_600);
lean_ctor_set(x_653, 1, x_652);
lean_ctor_set(x_653, 2, x_649);
lean_ctor_set(x_653, 3, x_599);
x_654 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_654, 0, x_653);
x_655 = l_Std_PersistentArray_empty___closed__1;
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
x_657 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_656, x_4, x_5, x_6, x_7, x_8, x_9, x_650);
x_658 = lean_ctor_get(x_657, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_659 = x_657;
} else {
 lean_dec_ref(x_657);
 x_659 = lean_box(0);
}
lean_inc(x_649);
x_660 = l_Lean_mkApp(x_592, x_649);
x_661 = lean_expr_instantiate1(x_634, x_649);
lean_dec(x_634);
x_662 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_662, 0, x_649);
if (lean_is_scalar(x_598)) {
 x_663 = lean_alloc_ctor(0, 4, 0);
} else {
 x_663 = x_598;
}
lean_ctor_set(x_663, 0, x_596);
lean_ctor_set(x_663, 1, x_25);
lean_ctor_set(x_663, 2, x_651);
lean_ctor_set(x_663, 3, x_662);
lean_ctor_set(x_3, 1, x_594);
lean_ctor_set(x_3, 0, x_663);
if (lean_is_scalar(x_646)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_646;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_3);
if (lean_is_scalar(x_595)) {
 x_665 = lean_alloc_ctor(0, 2, 0);
} else {
 x_665 = x_595;
}
lean_ctor_set(x_665, 0, x_660);
lean_ctor_set(x_665, 1, x_664);
if (lean_is_scalar(x_659)) {
 x_666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_666 = x_659;
}
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_658);
x_15 = x_666;
goto block_23;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_667 = lean_ctor_get(x_648, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_648, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_669 = x_648;
} else {
 lean_dec_ref(x_648);
 x_669 = lean_box(0);
}
if (lean_is_scalar(x_669)) {
 x_670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_670 = x_669;
}
lean_ctor_set(x_670, 0, x_667);
lean_ctor_set(x_670, 1, x_668);
x_15 = x_670;
goto block_23;
}
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_640);
lean_dec(x_636);
lean_dec(x_634);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_671 = lean_ctor_get(x_641, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_641, 1);
lean_inc(x_672);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_673 = x_641;
} else {
 lean_dec_ref(x_641);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 2, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_671);
lean_ctor_set(x_674, 1, x_672);
x_15 = x_674;
goto block_23;
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_635);
lean_dec(x_633);
x_675 = lean_ctor_get(x_637, 1);
lean_inc(x_675);
lean_dec(x_637);
x_676 = lean_ctor_get(x_638, 0);
lean_inc(x_676);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 x_677 = x_638;
} else {
 lean_dec_ref(x_638);
 x_677 = lean_box(0);
}
x_678 = l_Lean_mkHole(x_596);
if (lean_is_scalar(x_636)) {
 x_679 = lean_alloc_ctor(0, 1, 0);
} else {
 x_679 = x_636;
 lean_ctor_set_tag(x_679, 0);
}
lean_ctor_set(x_679, 0, x_678);
x_680 = lean_ctor_get(x_6, 1);
lean_inc(x_680);
lean_inc(x_676);
x_681 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_681, 0, x_600);
lean_ctor_set(x_681, 1, x_680);
lean_ctor_set(x_681, 2, x_676);
lean_ctor_set(x_681, 3, x_599);
x_682 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_682, 0, x_681);
x_683 = l_Std_PersistentArray_empty___closed__1;
x_684 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_684, 0, x_682);
lean_ctor_set(x_684, 1, x_683);
x_685 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_684, x_4, x_5, x_6, x_7, x_8, x_9, x_675);
x_686 = lean_ctor_get(x_685, 1);
lean_inc(x_686);
if (lean_is_exclusive(x_685)) {
 lean_ctor_release(x_685, 0);
 lean_ctor_release(x_685, 1);
 x_687 = x_685;
} else {
 lean_dec_ref(x_685);
 x_687 = lean_box(0);
}
lean_inc(x_676);
x_688 = l_Lean_mkApp(x_592, x_676);
x_689 = lean_expr_instantiate1(x_634, x_676);
lean_dec(x_634);
if (lean_is_scalar(x_677)) {
 x_690 = lean_alloc_ctor(1, 1, 0);
} else {
 x_690 = x_677;
}
lean_ctor_set(x_690, 0, x_676);
if (lean_is_scalar(x_598)) {
 x_691 = lean_alloc_ctor(0, 4, 0);
} else {
 x_691 = x_598;
}
lean_ctor_set(x_691, 0, x_596);
lean_ctor_set(x_691, 1, x_25);
lean_ctor_set(x_691, 2, x_679);
lean_ctor_set(x_691, 3, x_690);
lean_ctor_set(x_3, 1, x_594);
lean_ctor_set(x_3, 0, x_691);
if (lean_is_scalar(x_595)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_595;
}
lean_ctor_set(x_692, 0, x_689);
lean_ctor_set(x_692, 1, x_3);
x_693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_693, 0, x_688);
lean_ctor_set(x_693, 1, x_692);
if (lean_is_scalar(x_687)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_687;
}
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_686);
x_15 = x_694;
goto block_23;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_633);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_695 = lean_ctor_get(x_637, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_637, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_697 = x_637;
} else {
 lean_dec_ref(x_637);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
x_15 = x_698;
goto block_23;
}
}
default: 
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_699 = lean_ctor_get(x_601, 1);
lean_inc(x_699);
lean_dec(x_601);
x_700 = lean_ctor_get(x_602, 1);
lean_inc(x_700);
x_701 = lean_ctor_get(x_602, 2);
lean_inc(x_701);
lean_dec(x_602);
x_702 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_702, 0, x_700);
x_703 = lean_ctor_get(x_8, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_8, 1);
lean_inc(x_704);
x_705 = lean_ctor_get(x_8, 2);
lean_inc(x_705);
x_706 = lean_ctor_get(x_8, 3);
lean_inc(x_706);
x_707 = lean_ctor_get(x_8, 4);
lean_inc(x_707);
x_708 = lean_ctor_get(x_8, 5);
lean_inc(x_708);
x_709 = l_Lean_replaceRef(x_596, x_706);
lean_dec(x_706);
x_710 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_710, 0, x_703);
lean_ctor_set(x_710, 1, x_704);
lean_ctor_set(x_710, 2, x_705);
lean_ctor_set(x_710, 3, x_709);
lean_ctor_set(x_710, 4, x_707);
lean_ctor_set(x_710, 5, x_708);
x_711 = 0;
x_712 = lean_box(0);
lean_inc(x_6);
x_713 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_702, x_711, x_712, x_6, x_7, x_710, x_9, x_699);
lean_dec(x_710);
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_714);
x_717 = lean_ctor_get(x_6, 1);
lean_inc(x_717);
lean_inc(x_716);
x_718 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_718, 0, x_600);
lean_ctor_set(x_718, 1, x_717);
lean_ctor_set(x_718, 2, x_716);
lean_ctor_set(x_718, 3, x_599);
x_719 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_719, 0, x_718);
x_720 = l_Std_PersistentArray_empty___closed__1;
x_721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
x_722 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_721, x_4, x_5, x_6, x_7, x_8, x_9, x_715);
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 x_724 = x_722;
} else {
 lean_dec_ref(x_722);
 x_724 = lean_box(0);
}
lean_inc(x_716);
x_725 = l_Lean_mkApp(x_592, x_716);
x_726 = lean_expr_instantiate1(x_701, x_716);
lean_dec(x_701);
x_727 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_727, 0, x_716);
if (lean_is_scalar(x_598)) {
 x_728 = lean_alloc_ctor(0, 4, 0);
} else {
 x_728 = x_598;
}
lean_ctor_set(x_728, 0, x_596);
lean_ctor_set(x_728, 1, x_25);
lean_ctor_set(x_728, 2, x_597);
lean_ctor_set(x_728, 3, x_727);
lean_ctor_set(x_3, 1, x_594);
lean_ctor_set(x_3, 0, x_728);
if (lean_is_scalar(x_595)) {
 x_729 = lean_alloc_ctor(0, 2, 0);
} else {
 x_729 = x_595;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_3);
x_730 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_730, 0, x_725);
lean_ctor_set(x_730, 1, x_729);
if (lean_is_scalar(x_724)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_724;
}
lean_ctor_set(x_731, 0, x_730);
lean_ctor_set(x_731, 1, x_723);
x_15 = x_731;
goto block_23;
}
}
}
else
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_732 = lean_ctor_get(x_601, 1);
lean_inc(x_732);
lean_dec(x_601);
x_733 = l_Lean_indentExpr(x_602);
x_734 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
x_735 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
x_736 = l_Lean_KernelException_toMessageData___closed__15;
x_737 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
x_738 = lean_ctor_get(x_8, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_8, 1);
lean_inc(x_739);
x_740 = lean_ctor_get(x_8, 2);
lean_inc(x_740);
x_741 = lean_ctor_get(x_8, 3);
lean_inc(x_741);
x_742 = lean_ctor_get(x_8, 4);
lean_inc(x_742);
x_743 = lean_ctor_get(x_8, 5);
lean_inc(x_743);
x_744 = l_Lean_replaceRef(x_596, x_741);
lean_dec(x_741);
lean_dec(x_596);
x_745 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_745, 0, x_738);
lean_ctor_set(x_745, 1, x_739);
lean_ctor_set(x_745, 2, x_740);
lean_ctor_set(x_745, 3, x_744);
lean_ctor_set(x_745, 4, x_742);
lean_ctor_set(x_745, 5, x_743);
lean_inc(x_4);
lean_inc(x_1);
x_746 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_600, x_1, x_737, x_4, x_5, x_6, x_7, x_745, x_9, x_732);
lean_dec(x_745);
x_15 = x_746;
goto block_23;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_592);
lean_dec(x_25);
lean_free_object(x_3);
x_747 = lean_ctor_get(x_601, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_601, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_601)) {
 lean_ctor_release(x_601, 0);
 lean_ctor_release(x_601, 1);
 x_749 = x_601;
} else {
 lean_dec_ref(x_601);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
x_15 = x_750;
goto block_23;
}
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_751 = lean_ctor_get(x_13, 0);
lean_inc(x_751);
lean_dec(x_13);
x_752 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_753 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_751, x_752, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_751);
x_15 = x_753;
goto block_23;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_29);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_754 = lean_ctor_get(x_13, 0);
lean_inc(x_754);
lean_dec(x_13);
x_755 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_756 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_754, x_755, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_754);
x_15 = x_756;
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
x_2 = x_16;
x_3 = x_14;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_768; lean_object* x_769; 
x_757 = lean_ctor_get(x_3, 0);
x_758 = lean_ctor_get(x_3, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_3);
x_768 = lean_ctor_get(x_2, 1);
lean_inc(x_768);
x_769 = lean_ctor_get(x_757, 1);
lean_inc(x_769);
if (lean_obj_tag(x_769) == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_768);
lean_dec(x_2);
x_770 = lean_ctor_get(x_757, 0);
lean_inc(x_770);
lean_dec(x_757);
x_771 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_772 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_770, x_771, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_770);
x_759 = x_772;
goto block_767;
}
else
{
lean_object* x_773; 
x_773 = lean_ctor_get(x_769, 0);
lean_inc(x_773);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; 
x_774 = lean_ctor_get(x_769, 1);
lean_inc(x_774);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_775 = lean_ctor_get(x_2, 0);
lean_inc(x_775);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_776 = x_2;
} else {
 lean_dec_ref(x_2);
 x_776 = lean_box(0);
}
x_777 = lean_ctor_get(x_768, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_768, 1);
lean_inc(x_778);
if (lean_is_exclusive(x_768)) {
 lean_ctor_release(x_768, 0);
 lean_ctor_release(x_768, 1);
 x_779 = x_768;
} else {
 lean_dec_ref(x_768);
 x_779 = lean_box(0);
}
x_780 = lean_ctor_get(x_757, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_757, 2);
lean_inc(x_781);
if (lean_is_exclusive(x_757)) {
 lean_ctor_release(x_757, 0);
 lean_ctor_release(x_757, 1);
 lean_ctor_release(x_757, 2);
 lean_ctor_release(x_757, 3);
 x_782 = x_757;
} else {
 lean_dec_ref(x_757);
 x_782 = lean_box(0);
}
x_783 = lean_ctor_get(x_773, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_773, 1);
lean_inc(x_784);
lean_dec(x_773);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_785 = l_Lean_Meta_whnfForall(x_777, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
if (lean_obj_tag(x_786) == 7)
{
switch (lean_obj_tag(x_781)) {
case 0:
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; uint8_t x_793; lean_object* x_794; 
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
lean_dec(x_785);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
x_789 = lean_ctor_get(x_786, 2);
lean_inc(x_789);
lean_dec(x_786);
x_790 = lean_ctor_get(x_781, 0);
lean_inc(x_790);
x_791 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_791, 0, x_788);
x_792 = lean_box(0);
x_793 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_794 = l_Lean_Elab_Term_elabTermEnsuringType(x_790, x_791, x_793, x_792, x_4, x_5, x_6, x_7, x_8, x_9, x_787);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_795 = lean_ctor_get(x_794, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_794, 1);
lean_inc(x_796);
lean_dec(x_794);
x_797 = lean_ctor_get(x_6, 1);
lean_inc(x_797);
lean_inc(x_795);
x_798 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_798, 0, x_784);
lean_ctor_set(x_798, 1, x_797);
lean_ctor_set(x_798, 2, x_795);
lean_ctor_set(x_798, 3, x_783);
x_799 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_799, 0, x_798);
x_800 = l_Std_PersistentArray_empty___closed__1;
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
x_802 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_801, x_4, x_5, x_6, x_7, x_8, x_9, x_796);
x_803 = lean_ctor_get(x_802, 1);
lean_inc(x_803);
if (lean_is_exclusive(x_802)) {
 lean_ctor_release(x_802, 0);
 lean_ctor_release(x_802, 1);
 x_804 = x_802;
} else {
 lean_dec_ref(x_802);
 x_804 = lean_box(0);
}
lean_inc(x_795);
x_805 = l_Lean_mkApp(x_775, x_795);
x_806 = lean_expr_instantiate1(x_789, x_795);
lean_dec(x_789);
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_795);
if (lean_is_scalar(x_782)) {
 x_808 = lean_alloc_ctor(0, 4, 0);
} else {
 x_808 = x_782;
}
lean_ctor_set(x_808, 0, x_780);
lean_ctor_set(x_808, 1, x_769);
lean_ctor_set(x_808, 2, x_781);
lean_ctor_set(x_808, 3, x_807);
x_809 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_809, 0, x_808);
lean_ctor_set(x_809, 1, x_778);
if (lean_is_scalar(x_779)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_779;
}
lean_ctor_set(x_810, 0, x_806);
lean_ctor_set(x_810, 1, x_809);
if (lean_is_scalar(x_776)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_776;
}
lean_ctor_set(x_811, 0, x_805);
lean_ctor_set(x_811, 1, x_810);
if (lean_is_scalar(x_804)) {
 x_812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_812 = x_804;
}
lean_ctor_set(x_812, 0, x_811);
lean_ctor_set(x_812, 1, x_803);
x_759 = x_812;
goto block_767;
}
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_789);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_769);
x_813 = lean_ctor_get(x_794, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_794, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 x_815 = x_794;
} else {
 lean_dec_ref(x_794);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
x_759 = x_816;
goto block_767;
}
}
case 1:
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_817 = lean_ctor_get(x_785, 1);
lean_inc(x_817);
lean_dec(x_785);
x_818 = lean_ctor_get(x_786, 1);
lean_inc(x_818);
x_819 = lean_ctor_get(x_786, 2);
lean_inc(x_819);
lean_dec(x_786);
x_820 = lean_ctor_get(x_781, 0);
lean_inc(x_820);
if (lean_is_exclusive(x_781)) {
 lean_ctor_release(x_781, 0);
 x_821 = x_781;
} else {
 lean_dec_ref(x_781);
 x_821 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_818);
x_822 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_820, x_818, x_4, x_5, x_6, x_7, x_8, x_9, x_817);
if (lean_obj_tag(x_822) == 0)
{
lean_object* x_823; 
x_823 = lean_ctor_get(x_822, 0);
lean_inc(x_823);
if (lean_obj_tag(x_823) == 0)
{
lean_object* x_824; lean_object* x_825; lean_object* x_826; 
lean_dec(x_776);
x_824 = lean_ctor_get(x_822, 1);
lean_inc(x_824);
lean_dec(x_822);
x_825 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_825, 0, x_818);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_825);
x_826 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_820, x_825, x_4, x_5, x_6, x_7, x_8, x_9, x_824);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_ctor_get(x_827, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_827, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_831 = x_827;
} else {
 lean_dec_ref(x_827);
 x_831 = lean_box(0);
}
x_832 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_833 = l_Lean_Elab_Term_ensureHasType(x_825, x_829, x_832, x_4, x_5, x_6, x_7, x_8, x_9, x_828);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
if (lean_is_scalar(x_821)) {
 x_836 = lean_alloc_ctor(1, 1, 0);
} else {
 x_836 = x_821;
}
lean_ctor_set(x_836, 0, x_830);
x_837 = lean_ctor_get(x_6, 1);
lean_inc(x_837);
lean_inc(x_834);
x_838 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_838, 0, x_784);
lean_ctor_set(x_838, 1, x_837);
lean_ctor_set(x_838, 2, x_834);
lean_ctor_set(x_838, 3, x_783);
x_839 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_839, 0, x_838);
x_840 = l_Std_PersistentArray_empty___closed__1;
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
x_842 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_841, x_4, x_5, x_6, x_7, x_8, x_9, x_835);
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_844 = x_842;
} else {
 lean_dec_ref(x_842);
 x_844 = lean_box(0);
}
lean_inc(x_834);
x_845 = l_Lean_mkApp(x_775, x_834);
x_846 = lean_expr_instantiate1(x_819, x_834);
lean_dec(x_819);
x_847 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_847, 0, x_834);
if (lean_is_scalar(x_782)) {
 x_848 = lean_alloc_ctor(0, 4, 0);
} else {
 x_848 = x_782;
}
lean_ctor_set(x_848, 0, x_780);
lean_ctor_set(x_848, 1, x_769);
lean_ctor_set(x_848, 2, x_836);
lean_ctor_set(x_848, 3, x_847);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_778);
if (lean_is_scalar(x_831)) {
 x_850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_850 = x_831;
}
lean_ctor_set(x_850, 0, x_846);
lean_ctor_set(x_850, 1, x_849);
if (lean_is_scalar(x_779)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_779;
}
lean_ctor_set(x_851, 0, x_845);
lean_ctor_set(x_851, 1, x_850);
if (lean_is_scalar(x_844)) {
 x_852 = lean_alloc_ctor(0, 2, 0);
} else {
 x_852 = x_844;
}
lean_ctor_set(x_852, 0, x_851);
lean_ctor_set(x_852, 1, x_843);
x_759 = x_852;
goto block_767;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; 
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_821);
lean_dec(x_819);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_775);
lean_dec(x_769);
x_853 = lean_ctor_get(x_833, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_833, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_855 = x_833;
} else {
 lean_dec_ref(x_833);
 x_855 = lean_box(0);
}
if (lean_is_scalar(x_855)) {
 x_856 = lean_alloc_ctor(1, 2, 0);
} else {
 x_856 = x_855;
}
lean_ctor_set(x_856, 0, x_853);
lean_ctor_set(x_856, 1, x_854);
x_759 = x_856;
goto block_767;
}
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_dec(x_825);
lean_dec(x_821);
lean_dec(x_819);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_775);
lean_dec(x_769);
x_857 = lean_ctor_get(x_826, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_826, 1);
lean_inc(x_858);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_859 = x_826;
} else {
 lean_dec_ref(x_826);
 x_859 = lean_box(0);
}
if (lean_is_scalar(x_859)) {
 x_860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_860 = x_859;
}
lean_ctor_set(x_860, 0, x_857);
lean_ctor_set(x_860, 1, x_858);
x_759 = x_860;
goto block_767;
}
}
else
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_820);
lean_dec(x_818);
x_861 = lean_ctor_get(x_822, 1);
lean_inc(x_861);
lean_dec(x_822);
x_862 = lean_ctor_get(x_823, 0);
lean_inc(x_862);
if (lean_is_exclusive(x_823)) {
 lean_ctor_release(x_823, 0);
 x_863 = x_823;
} else {
 lean_dec_ref(x_823);
 x_863 = lean_box(0);
}
x_864 = l_Lean_mkHole(x_780);
if (lean_is_scalar(x_821)) {
 x_865 = lean_alloc_ctor(0, 1, 0);
} else {
 x_865 = x_821;
 lean_ctor_set_tag(x_865, 0);
}
lean_ctor_set(x_865, 0, x_864);
x_866 = lean_ctor_get(x_6, 1);
lean_inc(x_866);
lean_inc(x_862);
x_867 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_867, 0, x_784);
lean_ctor_set(x_867, 1, x_866);
lean_ctor_set(x_867, 2, x_862);
lean_ctor_set(x_867, 3, x_783);
x_868 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_868, 0, x_867);
x_869 = l_Std_PersistentArray_empty___closed__1;
x_870 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
x_871 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_870, x_4, x_5, x_6, x_7, x_8, x_9, x_861);
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_871)) {
 lean_ctor_release(x_871, 0);
 lean_ctor_release(x_871, 1);
 x_873 = x_871;
} else {
 lean_dec_ref(x_871);
 x_873 = lean_box(0);
}
lean_inc(x_862);
x_874 = l_Lean_mkApp(x_775, x_862);
x_875 = lean_expr_instantiate1(x_819, x_862);
lean_dec(x_819);
if (lean_is_scalar(x_863)) {
 x_876 = lean_alloc_ctor(1, 1, 0);
} else {
 x_876 = x_863;
}
lean_ctor_set(x_876, 0, x_862);
if (lean_is_scalar(x_782)) {
 x_877 = lean_alloc_ctor(0, 4, 0);
} else {
 x_877 = x_782;
}
lean_ctor_set(x_877, 0, x_780);
lean_ctor_set(x_877, 1, x_769);
lean_ctor_set(x_877, 2, x_865);
lean_ctor_set(x_877, 3, x_876);
x_878 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_778);
if (lean_is_scalar(x_779)) {
 x_879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_879 = x_779;
}
lean_ctor_set(x_879, 0, x_875);
lean_ctor_set(x_879, 1, x_878);
if (lean_is_scalar(x_776)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_776;
}
lean_ctor_set(x_880, 0, x_874);
lean_ctor_set(x_880, 1, x_879);
if (lean_is_scalar(x_873)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_873;
}
lean_ctor_set(x_881, 0, x_880);
lean_ctor_set(x_881, 1, x_872);
x_759 = x_881;
goto block_767;
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_821);
lean_dec(x_820);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_769);
x_882 = lean_ctor_get(x_822, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_822, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_822)) {
 lean_ctor_release(x_822, 0);
 lean_ctor_release(x_822, 1);
 x_884 = x_822;
} else {
 lean_dec_ref(x_822);
 x_884 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_885 = lean_alloc_ctor(1, 2, 0);
} else {
 x_885 = x_884;
}
lean_ctor_set(x_885, 0, x_882);
lean_ctor_set(x_885, 1, x_883);
x_759 = x_885;
goto block_767;
}
}
default: 
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; uint8_t x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_886 = lean_ctor_get(x_785, 1);
lean_inc(x_886);
lean_dec(x_785);
x_887 = lean_ctor_get(x_786, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_786, 2);
lean_inc(x_888);
lean_dec(x_786);
x_889 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_889, 0, x_887);
x_890 = lean_ctor_get(x_8, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_8, 1);
lean_inc(x_891);
x_892 = lean_ctor_get(x_8, 2);
lean_inc(x_892);
x_893 = lean_ctor_get(x_8, 3);
lean_inc(x_893);
x_894 = lean_ctor_get(x_8, 4);
lean_inc(x_894);
x_895 = lean_ctor_get(x_8, 5);
lean_inc(x_895);
x_896 = l_Lean_replaceRef(x_780, x_893);
lean_dec(x_893);
x_897 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_897, 0, x_890);
lean_ctor_set(x_897, 1, x_891);
lean_ctor_set(x_897, 2, x_892);
lean_ctor_set(x_897, 3, x_896);
lean_ctor_set(x_897, 4, x_894);
lean_ctor_set(x_897, 5, x_895);
x_898 = 0;
x_899 = lean_box(0);
lean_inc(x_6);
x_900 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_889, x_898, x_899, x_6, x_7, x_897, x_9, x_886);
lean_dec(x_897);
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_900, 1);
lean_inc(x_902);
lean_dec(x_900);
x_903 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_901);
x_904 = lean_ctor_get(x_6, 1);
lean_inc(x_904);
lean_inc(x_903);
x_905 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_905, 0, x_784);
lean_ctor_set(x_905, 1, x_904);
lean_ctor_set(x_905, 2, x_903);
lean_ctor_set(x_905, 3, x_783);
x_906 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_906, 0, x_905);
x_907 = l_Std_PersistentArray_empty___closed__1;
x_908 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
x_909 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_908, x_4, x_5, x_6, x_7, x_8, x_9, x_902);
x_910 = lean_ctor_get(x_909, 1);
lean_inc(x_910);
if (lean_is_exclusive(x_909)) {
 lean_ctor_release(x_909, 0);
 lean_ctor_release(x_909, 1);
 x_911 = x_909;
} else {
 lean_dec_ref(x_909);
 x_911 = lean_box(0);
}
lean_inc(x_903);
x_912 = l_Lean_mkApp(x_775, x_903);
x_913 = lean_expr_instantiate1(x_888, x_903);
lean_dec(x_888);
x_914 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_914, 0, x_903);
if (lean_is_scalar(x_782)) {
 x_915 = lean_alloc_ctor(0, 4, 0);
} else {
 x_915 = x_782;
}
lean_ctor_set(x_915, 0, x_780);
lean_ctor_set(x_915, 1, x_769);
lean_ctor_set(x_915, 2, x_781);
lean_ctor_set(x_915, 3, x_914);
x_916 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_916, 0, x_915);
lean_ctor_set(x_916, 1, x_778);
if (lean_is_scalar(x_779)) {
 x_917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_917 = x_779;
}
lean_ctor_set(x_917, 0, x_913);
lean_ctor_set(x_917, 1, x_916);
if (lean_is_scalar(x_776)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_776;
}
lean_ctor_set(x_918, 0, x_912);
lean_ctor_set(x_918, 1, x_917);
if (lean_is_scalar(x_911)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_911;
}
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_910);
x_759 = x_919;
goto block_767;
}
}
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_769);
x_920 = lean_ctor_get(x_785, 1);
lean_inc(x_920);
lean_dec(x_785);
x_921 = l_Lean_indentExpr(x_786);
x_922 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4;
x_923 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_923, 0, x_922);
lean_ctor_set(x_923, 1, x_921);
x_924 = l_Lean_KernelException_toMessageData___closed__15;
x_925 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_925, 0, x_923);
lean_ctor_set(x_925, 1, x_924);
x_926 = lean_ctor_get(x_8, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_8, 1);
lean_inc(x_927);
x_928 = lean_ctor_get(x_8, 2);
lean_inc(x_928);
x_929 = lean_ctor_get(x_8, 3);
lean_inc(x_929);
x_930 = lean_ctor_get(x_8, 4);
lean_inc(x_930);
x_931 = lean_ctor_get(x_8, 5);
lean_inc(x_931);
x_932 = l_Lean_replaceRef(x_780, x_929);
lean_dec(x_929);
lean_dec(x_780);
x_933 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_933, 0, x_926);
lean_ctor_set(x_933, 1, x_927);
lean_ctor_set(x_933, 2, x_928);
lean_ctor_set(x_933, 3, x_932);
lean_ctor_set(x_933, 4, x_930);
lean_ctor_set(x_933, 5, x_931);
lean_inc(x_4);
lean_inc(x_1);
x_934 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_784, x_1, x_925, x_4, x_5, x_6, x_7, x_933, x_9, x_920);
lean_dec(x_933);
x_759 = x_934;
goto block_767;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_769);
x_935 = lean_ctor_get(x_785, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_785, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_937 = x_785;
} else {
 lean_dec_ref(x_785);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
x_759 = x_938;
goto block_767;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_774);
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_2);
x_939 = lean_ctor_get(x_757, 0);
lean_inc(x_939);
lean_dec(x_757);
x_940 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_941 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_939, x_940, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_939);
x_759 = x_941;
goto block_767;
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_dec(x_773);
lean_dec(x_769);
lean_dec(x_768);
lean_dec(x_2);
x_942 = lean_ctor_get(x_757, 0);
lean_inc(x_942);
lean_dec(x_757);
x_943 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3;
lean_inc(x_8);
lean_inc(x_4);
x_944 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_942, x_943, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_942);
x_759 = x_944;
goto block_767;
}
}
block_767:
{
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
lean_dec(x_759);
x_2 = x_760;
x_3 = x_758;
x_10 = x_761;
goto _start;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_758);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_763 = lean_ctor_get(x_759, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_759, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_765 = x_759;
} else {
 lean_dec_ref(x_759);
 x_765 = lean_box(0);
}
if (lean_is_scalar(x_765)) {
 x_766 = lean_alloc_ctor(1, 2, 0);
} else {
 x_766 = x_765;
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_764);
return x_766;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
lean_ctor_set(x_7, 3, x_13);
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
x_19 = l_Lean_getStructureCtor(x_17, x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_29 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4(x_18, x_27, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_29, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 1);
x_37 = lean_ctor_get(x_31, 0);
lean_dec(x_37);
x_38 = l_List_reverse___rarg(x_36);
x_39 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_38);
lean_ctor_set(x_31, 1, x_39);
lean_ctor_set(x_31, 0, x_34);
lean_ctor_set(x_29, 0, x_31);
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
x_41 = l_List_reverse___rarg(x_40);
x_42 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_29, 0, x_43);
return x_29;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_dec(x_29);
x_45 = lean_ctor_get(x_30, 0);
lean_inc(x_45);
lean_dec(x_30);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_47 = x_31;
} else {
 lean_dec_ref(x_31);
 x_47 = lean_box(0);
}
x_48 = l_List_reverse___rarg(x_46);
x_49 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_29);
if (x_52 == 0)
{
return x_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_29, 0);
x_54 = lean_ctor_get(x_29, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_29);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
x_62 = lean_ctor_get(x_7, 2);
x_63 = lean_ctor_get(x_7, 3);
x_64 = lean_ctor_get(x_7, 4);
x_65 = lean_ctor_get(x_7, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_66 = l_Lean_replaceRef(x_10, x_63);
lean_dec(x_63);
lean_dec(x_10);
x_67 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_66);
lean_ctor_set(x_67, 4, x_64);
lean_ctor_set(x_67, 5, x_65);
x_68 = lean_st_ref_get(x_8, x_9);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_72);
x_73 = l_Lean_getStructureCtor(x_71, x_72);
lean_inc(x_8);
lean_inc(x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_74 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader(x_73, x_2, x_3, x_4, x_5, x_6, x_67, x_8, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_77);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_83 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4(x_72, x_81, x_82, x_3, x_4, x_5, x_6, x_67, x_8, x_76);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_87 = x_83;
} else {
 lean_dec_ref(x_83);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_84, 0);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_91 = l_List_reverse___rarg(x_89);
x_92 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_91);
if (lean_is_scalar(x_90)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_90;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_87)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_87;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_83, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_97 = x_83;
} else {
 lean_dec_ref(x_83);
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
lean_dec(x_72);
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_74, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_74, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_101 = x_74;
} else {
 lean_dec_ref(x_74);
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
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_pushInfoTree___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(x_6, x_1);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 1);
x_2 = x_9;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_4 = lean_array_push(x_2, x_3);
x_5 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_6 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_4 = lean_ctor_get(x_3, 2);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
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
x_12 = lean_ctor_get(x_2, 1);
x_2 = x_12;
goto _start;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f_match__3___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.StructInst.DefaultFields.findDefaultMissing?");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(623u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(x_1, x_4);
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2;
x_9 = lean_panic_fn(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_MetavarContext_isExprAssigned(x_1, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_17; 
lean_free_object(x_11);
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_11);
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_MetavarContext_isExprAssigned(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_2);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
return x_24;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_2);
x_5 = l_List_findSome_x3f___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_1);
return x_11;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.StructInst.DefaultFields.getFieldName");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1;
x_3 = lean_unsigned_to_nat(631u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_5 = lean_panic_fn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_instInhabitedName;
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_11 = lean_panic_fn(x_9, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lean_instInhabitedName;
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2;
x_14 = lean_panic_fn(x_12, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_4(x_2, x_4, x_5, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_15 = (uint8_t)((x_13 << 24) >> 61);
x_16 = l_Lean_BinderInfo_isExplicit(x_15);
if (x_16 == 0)
{
uint8_t x_98; 
x_98 = 0;
x_17 = x_98;
goto block_97;
}
else
{
uint8_t x_99; 
x_99 = 1;
x_17 = x_99;
goto block_97;
}
block_97:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 3);
x_20 = l_Lean_replaceRef(x_14, x_19);
lean_dec(x_19);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_20);
if (x_17 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_11);
x_22 = 0;
x_23 = lean_box(0);
lean_inc(x_5);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_23, x_5, x_6, x_7, x_8, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_expr_instantiate1(x_12, x_25);
lean_dec(x_25);
lean_dec(x_12);
x_2 = x_27;
x_9 = x_26;
goto _start;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_32);
x_33 = l_Lean_Meta_inferType(x_32, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_36 = l_Lean_Meta_isExprDefEq(x_34, x_11, x_5, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_expr_instantiate1(x_12, x_32);
lean_dec(x_32);
lean_dec(x_12);
x_2 = x_46;
x_9 = x_45;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
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
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
x_58 = lean_ctor_get(x_7, 2);
x_59 = lean_ctor_get(x_7, 3);
x_60 = lean_ctor_get(x_7, 4);
x_61 = lean_ctor_get(x_7, 5);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_7);
x_62 = l_Lean_replaceRef(x_14, x_59);
lean_dec(x_59);
lean_dec(x_14);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_58);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_63, 4, x_60);
lean_ctor_set(x_63, 5, x_61);
if (x_17 == 0)
{
lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_11);
x_65 = 0;
x_66 = lean_box(0);
lean_inc(x_5);
x_67 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_64, x_65, x_66, x_5, x_6, x_63, x_8, x_9);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_expr_instantiate1(x_12, x_68);
lean_dec(x_68);
lean_dec(x_12);
x_2 = x_70;
x_7 = x_63;
x_9 = x_69;
goto _start;
}
else
{
lean_object* x_72; 
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_10);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_9);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_72, 0);
lean_inc(x_75);
lean_dec(x_72);
lean_inc(x_8);
lean_inc(x_63);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_75);
x_76 = l_Lean_Meta_inferType(x_75, x_5, x_6, x_63, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_8);
lean_inc(x_63);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_Meta_isExprDefEq(x_77, x_11, x_5, x_6, x_63, x_8, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_75);
lean_dec(x_63);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_79, 1);
lean_inc(x_86);
lean_dec(x_79);
x_87 = lean_expr_instantiate1(x_12, x_75);
lean_dec(x_75);
lean_dec(x_12);
x_2 = x_87;
x_7 = x_63;
x_9 = x_86;
goto _start;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_dec(x_63);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_79, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_91 = x_79;
} else {
 lean_dec_ref(x_79);
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
lean_dec(x_75);
lean_dec(x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_100 = l_Lean_Meta_mkId___closed__2;
x_101 = lean_unsigned_to_nat(2u);
x_102 = l_Lean_Expr_isAppOfArity(x_2, x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_2);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_9);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_9);
return x_107;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = l_Lean_ConstantInfo_lparams(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = l_Lean_replaceRef(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_ctor_set(x_7, 3, x_14);
x_15 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_instantiate_value_lparams(x_2, x_16);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
x_22 = lean_ctor_get(x_7, 2);
x_23 = lean_ctor_get(x_7, 3);
x_24 = lean_ctor_get(x_7, 4);
x_25 = lean_ctor_get(x_7, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_7);
x_26 = l_Lean_replaceRef(x_10, x_23);
lean_dec(x_23);
lean_dec(x_10);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_26);
lean_ctor_set(x_27, 4, x_24);
lean_ctor_set(x_27, 5, x_25);
x_28 = l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_27, x_8, x_9);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_instantiate_value_lparams(x_2, x_29);
lean_dec(x_29);
x_32 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_31, x_3, x_4, x_5, x_6, x_27, x_8, x_30);
return x_32;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isApp(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Environment_getProjectionStructureName_x3f(x_17, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_1, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_box(0);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; 
lean_free_object(x_13);
x_23 = l_Lean_Meta_unfoldDefinition_x3f(x_2, x_3, x_4, x_5, x_6, x_16);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Environment_getProjectionStructureName_x3f(x_26, x_12);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Array_contains___at_Lean_findField_x3f___spec__1(x_1, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_unfoldDefinition_x3f(x_2, x_3, x_4, x_5, x_6, x_25);
return x_34;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_7);
return x_36;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; uint64_t x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_12 = lean_box_uint64(x_11);
x_13 = lean_apply_3(x_8, x_1, x_10, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_17 = lean_box_uint64(x_16);
x_18 = lean_apply_4(x_6, x_1, x_14, x_15, x_17);
return x_18;
}
case 6:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_5(x_2, x_1, x_19, x_20, x_21, x_23);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_29 = lean_box_uint64(x_28);
x_30 = lean_apply_5(x_3, x_1, x_25, x_26, x_27, x_29);
return x_30;
}
case 8:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_36 = lean_box_uint64(x_35);
x_37 = lean_apply_6(x_4, x_1, x_31, x_32, x_33, x_34, x_36);
return x_37;
}
case 10:
{
lean_object* x_38; lean_object* x_39; uint64_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_41 = lean_box_uint64(x_40);
x_42 = lean_apply_4(x_7, x_1, x_38, x_39, x_41);
return x_42;
}
case 11:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_47 = lean_box_uint64(x_46);
x_48 = lean_apply_5(x_5, x_1, x_43, x_44, x_45, x_47);
return x_48;
}
default: 
{
lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_apply_1(x_9, x_1);
return x_49;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce_match__4___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_11 = x_4;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = x_13;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = x_3 + x_20;
x_22 = x_18;
x_23 = lean_array_uset(x_15, x_3, x_22);
x_3 = x_21;
x_4 = x_23;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkLambdaFVars(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkForallFVars(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_getExprMVarAssignment_x3f(x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_8);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_18);
return x_9;
}
else
{
lean_free_object(x_9);
x_2 = x_18;
x_7 = x_16;
goto _start;
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
lean_object* x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
x_2 = x_22;
x_7 = x_21;
goto _start;
}
}
}
}
case 5:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn(x_26);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_30, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_isLambda(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux(x_2, x_35);
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_38, x_40);
x_42 = lean_array_get_size(x_41);
x_43 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_44 = x_41;
x_45 = lean_box_usize(x_43);
x_46 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1;
x_47 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1___boxed), 9, 4);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_45);
lean_closure_set(x_47, 2, x_46);
lean_closure_set(x_47, 3, x_44);
x_48 = x_47;
x_49 = lean_apply_5(x_48, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_Lean_mkAppN(x_32, x_51);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = l_Lean_mkAppN(x_32, x_53);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_32);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_getAppNumArgsAux(x_2, x_61);
x_63 = lean_mk_empty_array_with_capacity(x_62);
lean_dec(x_62);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(x_2, x_63);
x_65 = l_Lean_Expr_betaRev(x_32, x_64);
lean_dec(x_64);
lean_dec(x_32);
x_2 = x_65;
x_7 = x_33;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_31);
if (x_67 == 0)
{
return x_31;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_31, 0);
x_69 = lean_ctor_get(x_31, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_31);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_26);
lean_dec(x_2);
x_71 = lean_ctor_get(x_27, 1);
lean_inc(x_71);
lean_dec(x_27);
x_72 = lean_ctor_get(x_28, 0);
lean_inc(x_72);
lean_dec(x_28);
x_2 = x_72;
x_7 = x_71;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_27);
if (x_74 == 0)
{
return x_27;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_27, 0);
x_76 = lean_ctor_get(x_27, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_27);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
case 6:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1), 8, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_78, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
case 7:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__2), 8, 1);
lean_closure_set(x_80, 0, x_1);
x_81 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_2, x_80, x_3, x_4, x_5, x_6, x_7);
return x_81;
}
case 8:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___lambda__1), 8, 1);
lean_closure_set(x_82, 0, x_1);
x_83 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferLambdaType___spec__1___rarg(x_2, x_82, x_3, x_4, x_5, x_6, x_7);
return x_83;
}
case 10:
{
lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
x_86 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_85);
x_87 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_85, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_96; 
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
x_96 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_box(0);
x_91 = x_97;
goto block_95;
}
else
{
uint8_t x_98; 
lean_dec(x_96);
x_98 = l_Lean_Expr_isMVar(x_88);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_90);
lean_dec(x_85);
lean_dec(x_84);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_89);
return x_99;
}
else
{
lean_object* x_100; 
x_100 = lean_box(0);
x_91 = x_100;
goto block_95;
}
}
block_95:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_91);
x_92 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_92, 0, x_84);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set_uint64(x_92, sizeof(void*)*2, x_86);
x_93 = lean_expr_update_mdata(x_92, x_88);
if (lean_is_scalar(x_90)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_90;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
}
else
{
uint8_t x_101; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
return x_87;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_87, 0);
x_103 = lean_ctor_get(x_87, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_87);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 11:
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_2);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_2, 0);
x_107 = lean_ctor_get(x_2, 1);
x_108 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_108);
x_109 = l_Lean_Meta_project_x3f(x_108, x_107, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_108);
x_112 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_108, x_3, x_4, x_5, x_6, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_expr_update_proj(x_2, x_114);
lean_ctor_set(x_112, 0, x_115);
return x_112;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_112);
x_118 = lean_expr_update_proj(x_2, x_116);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
uint8_t x_120; 
lean_free_object(x_2);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
return x_112;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_112, 0);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_112);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_free_object(x_2);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
lean_dec(x_109);
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
lean_dec(x_110);
x_2 = x_125;
x_7 = x_124;
goto _start;
}
}
else
{
uint8_t x_127; 
lean_free_object(x_2);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_109);
if (x_127 == 0)
{
return x_109;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_109, 0);
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_109);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint64_t x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_2, 0);
x_132 = lean_ctor_get(x_2, 1);
x_133 = lean_ctor_get(x_2, 2);
x_134 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_133);
x_135 = l_Lean_Meta_project_x3f(x_133, x_132, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_133);
x_138 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_1, x_133, x_3, x_4, x_5, x_6, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_142, 0, x_131);
lean_ctor_set(x_142, 1, x_132);
lean_ctor_set(x_142, 2, x_133);
lean_ctor_set_uint64(x_142, sizeof(void*)*3, x_134);
x_143 = lean_expr_update_proj(x_142, x_139);
if (lean_is_scalar(x_141)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_141;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_140);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
x_145 = lean_ctor_get(x_138, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_138, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_147 = x_138;
} else {
 lean_dec_ref(x_138);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
lean_dec(x_135);
x_150 = lean_ctor_get(x_136, 0);
lean_inc(x_150);
lean_dec(x_136);
x_2 = x_150;
x_7 = x_149;
goto _start;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_ctor_get(x_135, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_135, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_154 = x_135;
} else {
 lean_dec_ref(x_135);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
default: 
{
lean_object* x_156; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_7);
return x_156;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop_match__3___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(lean_object* x_1) {
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
x_1 = lean_mk_string("_default");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_array_fget(x_1, x_6);
x_22 = l_Lean_Elab_Term_StructInst_Struct_structName(x_21);
lean_inc(x_4);
x_23 = l_Lean_Name_append(x_22, x_4);
lean_dec(x_22);
x_24 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2;
x_25 = l_Lean_Name_append(x_23, x_24);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_13, x_14);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_environment_find(x_29, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_21);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_6, x_31);
lean_dec(x_6);
x_6 = x_32;
x_14 = x_28;
goto _start;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_st_ref_get(x_13, x_28);
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
x_41 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_21, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_39);
lean_dec(x_34);
lean_dec(x_21);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Meta_setMCtx(x_40, x_10, x_11, x_12, x_13, x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_6, x_46);
lean_dec(x_6);
x_48 = lean_nat_add(x_7, x_46);
lean_dec(x_7);
x_6 = x_47;
x_7 = x_48;
x_14 = x_45;
goto _start;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = !lean_is_exclusive(x_42);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_53 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_2, x_52, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; size_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = 8192;
x_57 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3;
x_58 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_54);
x_59 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_57, x_56, x_54, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_61 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_55);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
lean_dec(x_62);
lean_ctor_set(x_42, 0, x_64);
x_65 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_66 = l_Lean_Elab_Term_ensureHasType(x_42, x_54, x_65, x_8, x_9, x_10, x_11, x_12, x_13, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Meta_assignExprMVar(x_5, x_67, x_10, x_11, x_12, x_13, x_68);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
lean_dec(x_71);
x_72 = 1;
x_73 = lean_box(x_72);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 1);
lean_inc(x_74);
lean_dec(x_69);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
return x_66;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_66, 0);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_60);
lean_dec(x_54);
lean_free_object(x_42);
x_82 = l_Lean_Meta_setMCtx(x_40, x_10, x_11, x_12, x_13, x_55);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_add(x_6, x_84);
lean_dec(x_6);
x_86 = lean_nat_add(x_7, x_84);
lean_dec(x_7);
x_6 = x_85;
x_7 = x_86;
x_14 = x_83;
goto _start;
}
}
else
{
uint8_t x_88; 
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
x_88 = !lean_is_exclusive(x_53);
if (x_88 == 0)
{
return x_53;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_53, 0);
x_90 = lean_ctor_get(x_53, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_53);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_42, 0);
lean_inc(x_92);
lean_dec(x_42);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_93 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce(x_2, x_92, x_10, x_11, x_12, x_13, x_50);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; size_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = 8192;
x_97 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3;
x_98 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_94);
x_99 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_97, x_96, x_94, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_101 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_95);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_ctor_get(x_102, 2);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_107 = l_Lean_Elab_Term_ensureHasType(x_105, x_94, x_106, x_8, x_9, x_10, x_11, x_12, x_13, x_103);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Meta_assignExprMVar(x_5, x_108, x_10, x_11, x_12, x_13, x_109);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = 1;
x_114 = lean_box(x_113);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_107, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_118 = x_107;
} else {
 lean_dec_ref(x_107);
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
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_100);
lean_dec(x_94);
x_120 = l_Lean_Meta_setMCtx(x_40, x_10, x_11, x_12, x_13, x_95);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_6, x_122);
lean_dec(x_6);
x_124 = lean_nat_add(x_7, x_122);
lean_dec(x_7);
x_6 = x_123;
x_7 = x_124;
x_14 = x_121;
goto _start;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
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
x_126 = lean_ctor_get(x_93, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_93, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_128 = x_93;
} else {
 lean_dec_ref(x_93);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
}
else
{
uint8_t x_130; 
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
x_130 = !lean_is_exclusive(x_41);
if (x_130 == 0)
{
return x_41;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_41, 0);
x_132 = lean_ctor_get(x_41, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_41);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_34);
lean_dec(x_21);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_add(x_6, x_134);
lean_dec(x_6);
x_6 = x_135;
x_14 = x_28;
goto _start;
}
}
}
}
else
{
uint8_t x_137; lean_object* x_138; lean_object* x_139; 
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
x_137 = 0;
x_138 = lean_box(x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_14);
return x_139;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_1, x_2, x_3, x_4, x_5, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_8 = lean_box_uint64(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_step_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_step_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_step_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_step_match__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Elab.Term.StructInst.DefaultFields.step");
return x_1;
}
}
static lean_object* _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4;
x_2 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1;
x_3 = lean_unsigned_to_nat(754u);
x_4 = lean_unsigned_to_nat(25u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
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
else
{
lean_object* x_25; 
lean_dec(x_12);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_26 = l_instInhabitedPUnit;
x_27 = l_instInhabited___rarg(x_2, x_26);
x_28 = lean_alloc_closure((void*)(l_instInhabitedReaderT___rarg___boxed), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2;
x_30 = lean_panic_fn(x_28, x_29);
x_31 = lean_apply_9(x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
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
lean_dec(x_2);
x_42 = lean_ctor_get(x_25, 0);
lean_inc(x_42);
lean_dec(x_25);
x_43 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_42);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
if (lean_obj_tag(x_46) == 2)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Elab_Term_isExprMVarAssigned(x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 2);
lean_inc(x_55);
lean_dec(x_3);
x_56 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_9);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_9, 3);
x_59 = l_Lean_replaceRef(x_52, x_58);
lean_dec(x_58);
lean_dec(x_52);
lean_ctor_set(x_9, 3, x_59);
x_60 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_61 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_53, x_54, x_55, x_56, x_47, x_60, x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_51);
lean_dec(x_55);
lean_dec(x_53);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; 
lean_dec(x_10);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_dec(x_65);
x_66 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_st_ref_get(x_10, x_70);
lean_dec(x_10);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_st_ref_take(x_4, x_72);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = 1;
x_76 = lean_box(x_75);
x_77 = lean_st_ref_set(x_4, x_76, x_74);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_10);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_61);
if (x_84 == 0)
{
return x_61;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_61, 0);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_61);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
x_90 = lean_ctor_get(x_9, 2);
x_91 = lean_ctor_get(x_9, 3);
x_92 = lean_ctor_get(x_9, 4);
x_93 = lean_ctor_get(x_9, 5);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_94 = l_Lean_replaceRef(x_52, x_91);
lean_dec(x_91);
lean_dec(x_52);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_89);
lean_ctor_set(x_95, 2, x_90);
lean_ctor_set(x_95, 3, x_94);
lean_ctor_set(x_95, 4, x_92);
lean_ctor_set(x_95, 5, x_93);
x_96 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_97 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop(x_53, x_54, x_55, x_56, x_47, x_96, x_96, x_5, x_6, x_7, x_8, x_95, x_10, x_51);
lean_dec(x_55);
lean_dec(x_53);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_10);
lean_dec(x_4);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = lean_st_ref_get(x_10, x_104);
lean_dec(x_10);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_st_ref_take(x_4, x_106);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = 1;
x_110 = lean_box(x_109);
x_111 = lean_st_ref_set(x_4, x_110, x_108);
lean_dec(x_4);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
lean_dec(x_4);
x_116 = lean_ctor_get(x_97, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_97, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_118 = x_97;
} else {
 lean_dec_ref(x_97);
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
else
{
uint8_t x_120; 
lean_dec(x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_48);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_48, 0);
lean_dec(x_121);
x_122 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_48, 0, x_122);
return x_48;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_48, 1);
lean_inc(x_123);
lean_dec(x_48);
x_124 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_46);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_11);
return x_127;
}
}
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_10(x_15, lean_box(0), x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(x_1, x_2, x_17, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_10(x_14, lean_box(0), x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_4);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1), 11, 3);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_4);
x_20 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__2), 12, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_4);
x_21 = lean_apply_12(x_18, lean_box(0), lean_box(0), x_19, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_array_push(x_17, x_1);
lean_ctor_set(x_2, 0, x_18);
x_19 = l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1;
x_20 = lean_box(0);
x_21 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(x_19, x_15, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_ctor_get(x_2, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_33 = lean_array_push(x_30, x_1);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_32);
x_35 = l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1;
x_36 = lean_box(0);
x_37 = l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1(x_35, x_15, x_36, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_39 = x_37;
} else {
 lean_dec_ref(x_37);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
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
else
{
uint8_t x_45; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_11, 0, x_47);
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 3);
x_14 = l_Lean_replaceRef(x_1, x_13);
lean_dec(x_13);
lean_ctor_set(x_9, 3, x_14);
x_15 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
x_18 = lean_ctor_get(x_9, 2);
x_19 = lean_ctor_get(x_9, 3);
x_20 = lean_ctor_get(x_9, 4);
x_21 = lean_ctor_get(x_9, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_22 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23, x_10, x_11);
lean_dec(x_23);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_st_ref_get(x_11, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_9, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(x_19, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
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
x_21 = lean_box(0);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_free_object(x_15);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_dec_lt(x_1, x_2);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_22);
x_24 = !lean_is_exclusive(x_4);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_4, 2);
lean_dec(x_25);
lean_inc(x_2);
lean_ctor_set(x_4, 2, x_2);
x_26 = lean_st_ref_get(x_11, x_18);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_5, x_27);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = 0;
x_31 = lean_box(x_30);
x_32 = lean_st_ref_set(x_5, x_31, x_29);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_34 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_st_ref_get(x_11, x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_5, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_2, x_42);
lean_dec(x_2);
x_2 = x_43;
x_12 = x_41;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_2);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
x_46 = lean_unsigned_to_nat(0u);
x_2 = x_46;
x_12 = x_45;
goto _start;
}
}
else
{
uint8_t x_48; 
lean_dec(x_4);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_4, 0);
x_53 = lean_ctor_get(x_4, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_4);
lean_inc(x_2);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_2);
x_55 = lean_st_ref_get(x_11, x_18);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_take(x_5, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = 0;
x_60 = lean_box(x_59);
x_61 = lean_st_ref_set(x_5, x_60, x_58);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_54);
lean_inc(x_3);
x_63 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_3, x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_st_ref_get(x_11, x_64);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_st_ref_get(x_5, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_add(x_2, x_71);
lean_dec(x_2);
x_2 = x_72;
x_4 = x_54;
x_12 = x_70;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_2);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_unsigned_to_nat(0u);
x_2 = x_75;
x_4 = x_54;
x_12 = x_74;
goto _start;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_79 = x_63;
} else {
 lean_dec_ref(x_63);
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
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_22, 0);
lean_inc(x_81);
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_22);
lean_dec(x_22);
x_83 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_85 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2;
x_87 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(x_81, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_81);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_15, 0);
x_90 = lean_ctor_get(x_15, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_15);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(x_91, x_3);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
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
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_nat_dec_lt(x_1, x_2);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
x_97 = lean_ctor_get(x_4, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_4, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_99 = x_4;
} else {
 lean_dec_ref(x_4);
 x_99 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 3, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_2);
x_101 = lean_st_ref_get(x_11, x_90);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = lean_st_ref_take(x_5, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = 0;
x_106 = lean_box(x_105);
x_107 = lean_st_ref_set(x_5, x_106, x_104);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_100);
lean_inc(x_3);
x_109 = l_Lean_Elab_Term_StructInst_DefaultFields_step(x_3, x_100, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_st_ref_get(x_11, x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_st_ref_get(x_5, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_nat_add(x_2, x_117);
lean_dec(x_2);
x_2 = x_118;
x_4 = x_100;
x_12 = x_116;
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; 
lean_dec(x_2);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
lean_dec(x_113);
x_121 = lean_unsigned_to_nat(0u);
x_2 = x_121;
x_4 = x_100;
x_12 = x_120;
goto _start;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_100);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_109, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_125 = x_109;
} else {
 lean_dec_ref(x_109);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_95, 0);
lean_inc(x_127);
x_128 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_95);
lean_dec(x_95);
x_129 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2;
x_133 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(x_127, x_133, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_90);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_127);
return x_134;
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(x_1);
x_10 = l_Array_empty___closed__1;
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
lean_dec(x_9);
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
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_6, 3);
x_10 = lean_ctor_get(x_2, 3);
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
lean_object* l_Std_fmt___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_formatStruct(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView(x_1, x_2, x_3);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandStruct(x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_69 = lean_st_ref_get(x_11, x_21);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 3);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*1);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_dec(x_69);
x_74 = 0;
x_22 = x_74;
x_23 = x_73;
goto block_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
x_77 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_76, x_6, x_7, x_8, x_9, x_10, x_11, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_unbox(x_78);
lean_dec(x_78);
x_22 = x_80;
x_23 = x_79;
goto block_68;
}
block_68:
{
if (x_22 == 0)
{
lean_object* x_24; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_20, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_28, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_27);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_27);
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
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
return x_24;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_24, 0);
x_40 = lean_ctor_get(x_24, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_24);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_inc(x_20);
x_42 = l_Lean_Elab_Term_StructInst_formatStruct(x_20);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
x_48 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_47, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_50 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct(x_20, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_54, x_6, x_7, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_53);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_50);
if (x_64 == 0)
{
return x_50;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_50, 0);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_50);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_81 = !lean_is_exclusive(x_19);
if (x_81 == 0)
{
return x_19;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_19, 0);
x_83 = lean_ctor_get(x_19, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_19);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, '");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_11 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_st_ref_get(x_9, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_12);
x_18 = l_Lean_isStructureLike(x_17, x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_20 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(x_1, x_12, x_3, x_2, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_16);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_apply_2(x_5, x_1, x_2);
return x_6;
}
else
{
lean_dec(x_5);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_apply_3(x_3, x_7, x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_2(x_4, x_11, x_2);
return x_12;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, explicit source is required when using '[<index>] := <value>'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_13 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
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
x_25 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_26 = l_Lean_throwError___at_Lean_Elab_Term_synthesizeInst___spec__1(x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_10, 1);
lean_inc(x_35);
lean_dec(x_10);
x_36 = lean_ctor_get(x_11, 0);
lean_inc(x_36);
lean_dec(x_11);
lean_inc(x_36);
lean_inc(x_1);
x_37 = lean_alloc_closure((void*)(l_Lean_Elab_Term_adaptExpander___lambda__1), 10, 3);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_36);
lean_closure_set(x_37, 2, x_2);
x_38 = l_Lean_Elab_withMacroExpansionInfo___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1(x_1, x_36, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
return x_38;
}
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst), 9, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_265____closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_6666_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Parser_Term(lean_object*);
lean_object* initialize_Lean_Elab_App(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_StructInst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_expandStructInstExpectedType(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNonAtomicExplicitSource___closed__4);
l_Lean_Elab_Term_StructInst_instInhabitedSource = _init_l_Lean_Elab_Term_StructInst_instInhabitedSource();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedSource);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__5);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructSource___closed__6);
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
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__4);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__5);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__7);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__8);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__9);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__10);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__11);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__12);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__13);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__14);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__15);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__16);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__17);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabModifyOp___closed__18);
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
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getStructName___rarg___closed__2);
l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1 = _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS___closed__1);
l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS = _init_l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instInhabitedFieldLHS);
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
l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1 = _init_l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1();
lean_mark_persistent(l_List_map___at_Lean_Elab_Term_StructInst_formatStruct___spec__1___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__2);
l_Lean_Elab_Term_StructInst_formatStruct___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatStruct___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___closed__3);
l_Lean_Elab_Term_StructInst_instToFormatStruct = _init_l_Lean_Elab_Term_StructInst_instToFormatStruct();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToFormatStruct);
l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1 = _init_l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_instToStringStruct___closed__1);
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
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_toFieldLHS___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkStructView___spec__2___closed__1);
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
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandNumLitFields___spec__3___closed__7);
l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1 = _init_l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1();
lean_mark_persistent(l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__1);
l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2 = _init_l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2();
lean_mark_persistent(l_List_map___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__1___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__1);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__2);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__3);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__4);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__5);
l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6 = _init_l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_expandParentFields___spec__2___closed__6);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__1);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__2);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__3);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__4);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__5);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___spec__12___closed__6);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkFieldMap___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_getFieldIdx___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_groupFields___lambda__3___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_addMissingFields___closed__1);
l_Lean_Elab_Term_StructInst_CtorHeaderResult_instMVars___default = _init_l_Lean_Elab_Term_StructInst_CtorHeaderResult_instMVars___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_CtorHeaderResult_instMVars___default);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_mkCtorHeaderAux___closed__3);
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
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__1);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__2);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__3);
l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4 = _init_l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4();
lean_mark_persistent(l_List_foldlM___at___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStruct___spec__4___closed__4);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_structs___default);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_allStructNames___default);
l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_Context_maxDistance___default);
l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default = _init_l_Lean_Elab_Term_StructInst_DefaultFields_State_progress___default();
l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___lambda__1___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___boxed__const__1);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault_loop___closed__3);
l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1 = _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__1);
l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2 = _init_l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_forIn_loop___at_Lean_Elab_Term_StructInst_DefaultFields_step___spec__1___lambda__1___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_step___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__1);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__2);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__3);
l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4 = _init_l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_0__Lean_Elab_Term_StructInst_elabStructInstAux___closed__4);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__2 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__2);
l_Lean_Elab_Term_StructInst_elabStructInst___closed__3 = _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_elabStructInst___closed__3);
l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1 = _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1);
res = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Term_StructInst_initFn____x40_Lean_Elab_StructInst___hyg_6666_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
