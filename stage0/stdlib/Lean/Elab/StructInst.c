// Lean compiler output
// Module: Lean.Elab.StructInst
// Imports: Init Lean.Util.FindExpr Lean.Elab.App Lean.Elab.Binders Lean.Elab.Quotation
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
extern lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4;
lean_object* l_Lean_Elab_Term_mkFreshExprMVar(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___boxed(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7___boxed(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_get_expr_assignment(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(size_t, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
extern lean_object* l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2;
lean_object* l_Std_HashMap_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4;
lean_object* l_Lean_Meta_forallTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
extern lean_object* l_Lean_formatKVMap___closed__1;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatField(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
lean_object* l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkId___closed__1;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
extern lean_object* l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
extern lean_object* l_Id_monad;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_27__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_inhabited;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__4;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1;
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getOptions(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_inhabited;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3___boxed(lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object*);
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_StructInst_7__mkStructView(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24;
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logTrace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1;
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields(lean_object*);
extern lean_object* l_Lean_Parser_Term_let___elambda__1___closed__2;
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
extern lean_object* l_Lean_Parser_Term_structInstField___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
lean_object* l_Lean_Elab_Term_setMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHole(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_environment_main_module(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object*);
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_letIdDecl___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
lean_object* l_Lean_Elab_Term_whnfForall(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PUnit_Inhabited;
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isSubobjectField_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Source_isNone(lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat;
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1;
extern lean_object* l_Lean_Parser_Term_structInst___elambda__1___closed__7;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__4;
lean_object* l_Lean_Elab_Term_isLocalTermId_x3f(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___boxed(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__2;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
extern lean_object* l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isIdent(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object*);
lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("src");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 5);
x_9 = lean_nat_add(x_8, x_4);
lean_ctor_set(x_3, 5, x_9);
if (x_6 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 8);
lean_dec(x_11);
lean_ctor_set(x_2, 8, x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_5, x_12);
x_14 = 0;
lean_inc(x_13);
x_15 = l_Lean_Elab_Term_isLocalTermId_x3f(x_13, x_14, x_2, x_3);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getMainModule___rarg(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_25 = l_Lean_addMacroScope(x_22, x_24, x_19);
x_26 = lean_box(0);
x_27 = l_Lean_SourceInfo_inhabited___closed__1;
x_28 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_26);
x_30 = l_Array_empty___closed__1;
x_31 = lean_array_push(x_30, x_29);
x_32 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_33 = lean_array_push(x_31, x_32);
x_34 = l_Lean_mkTermIdFromIdent___closed__2;
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Syntax_setArg(x_5, x_12, x_35);
x_37 = l_Lean_Syntax_setArg(x_1, x_4, x_36);
x_38 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_23);
lean_dec(x_2);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Elab_Term_getMainModule___rarg(x_40);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_addMacroScope(x_43, x_24, x_39);
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_27);
lean_ctor_set(x_45, 1, x_28);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_26);
x_46 = lean_array_push(x_30, x_45);
x_47 = lean_array_push(x_46, x_32);
x_48 = lean_array_push(x_47, x_32);
x_49 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_50 = lean_array_push(x_48, x_49);
x_51 = lean_array_push(x_50, x_13);
x_52 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_55 = lean_array_push(x_54, x_53);
x_56 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_57 = lean_array_push(x_55, x_56);
x_58 = lean_array_push(x_57, x_37);
x_59 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_41, 0, x_61);
return x_41;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_62 = lean_ctor_get(x_41, 0);
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_41);
x_64 = l_Lean_addMacroScope(x_62, x_24, x_39);
x_65 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_65, 0, x_27);
lean_ctor_set(x_65, 1, x_28);
lean_ctor_set(x_65, 2, x_64);
lean_ctor_set(x_65, 3, x_26);
x_66 = lean_array_push(x_30, x_65);
x_67 = lean_array_push(x_66, x_32);
x_68 = lean_array_push(x_67, x_32);
x_69 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_array_push(x_70, x_13);
x_72 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_75 = lean_array_push(x_74, x_73);
x_76 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_37);
x_79 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_63);
return x_82;
}
}
else
{
uint8_t x_83; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_15, 0);
lean_dec(x_84);
x_85 = lean_box(0);
lean_ctor_set(x_15, 0, x_85);
return x_15;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_15, 1);
lean_inc(x_86);
lean_dec(x_15);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get(x_2, 1);
x_91 = lean_ctor_get(x_2, 2);
x_92 = lean_ctor_get(x_2, 3);
x_93 = lean_ctor_get(x_2, 4);
x_94 = lean_ctor_get(x_2, 5);
x_95 = lean_ctor_get(x_2, 6);
x_96 = lean_ctor_get(x_2, 7);
x_97 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_98 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_99 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_100 = lean_ctor_get(x_2, 9);
lean_inc(x_100);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_2);
x_101 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_101, 0, x_89);
lean_ctor_set(x_101, 1, x_90);
lean_ctor_set(x_101, 2, x_91);
lean_ctor_set(x_101, 3, x_92);
lean_ctor_set(x_101, 4, x_93);
lean_ctor_set(x_101, 5, x_94);
lean_ctor_set(x_101, 6, x_95);
lean_ctor_set(x_101, 7, x_96);
lean_ctor_set(x_101, 8, x_8);
lean_ctor_set(x_101, 9, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*10, x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*10 + 1, x_98);
lean_ctor_set_uint8(x_101, sizeof(void*)*10 + 2, x_99);
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Syntax_getArg(x_5, x_102);
x_104 = 0;
lean_inc(x_103);
x_105 = l_Lean_Elab_Term_isLocalTermId_x3f(x_103, x_104, x_101, x_3);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Elab_Term_getCurrMacroScope(x_101, x_107);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lean_Elab_Term_getMainModule___rarg(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_115 = l_Lean_addMacroScope(x_112, x_114, x_109);
x_116 = lean_box(0);
x_117 = l_Lean_SourceInfo_inhabited___closed__1;
x_118 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_119 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_115);
lean_ctor_set(x_119, 3, x_116);
x_120 = l_Array_empty___closed__1;
x_121 = lean_array_push(x_120, x_119);
x_122 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_123 = lean_array_push(x_121, x_122);
x_124 = l_Lean_mkTermIdFromIdent___closed__2;
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l_Lean_Syntax_setArg(x_5, x_102, x_125);
x_127 = l_Lean_Syntax_setArg(x_1, x_4, x_126);
x_128 = l_Lean_Elab_Term_getCurrMacroScope(x_101, x_113);
lean_dec(x_101);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Elab_Term_getMainModule___rarg(x_130);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = l_Lean_addMacroScope(x_132, x_114, x_129);
x_136 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_136, 0, x_117);
lean_ctor_set(x_136, 1, x_118);
lean_ctor_set(x_136, 2, x_135);
lean_ctor_set(x_136, 3, x_116);
x_137 = lean_array_push(x_120, x_136);
x_138 = lean_array_push(x_137, x_122);
x_139 = lean_array_push(x_138, x_122);
x_140 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_141 = lean_array_push(x_139, x_140);
x_142 = lean_array_push(x_141, x_103);
x_143 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_146 = lean_array_push(x_145, x_144);
x_147 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_148 = lean_array_push(x_146, x_147);
x_149 = lean_array_push(x_148, x_127);
x_150 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
if (lean_is_scalar(x_134)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_134;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_133);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_106);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_5);
lean_dec(x_1);
x_154 = lean_ctor_get(x_105, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_155 = x_105;
} else {
 lean_dec_ref(x_105);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_3);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_3, 0);
x_161 = lean_ctor_get(x_3, 1);
x_162 = lean_ctor_get(x_3, 2);
x_163 = lean_ctor_get(x_3, 3);
x_164 = lean_ctor_get(x_3, 4);
x_165 = lean_ctor_get(x_3, 5);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_3);
x_166 = lean_nat_add(x_165, x_4);
x_167 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_161);
lean_ctor_set(x_167, 2, x_162);
lean_ctor_set(x_167, 3, x_163);
lean_ctor_set(x_167, 4, x_164);
lean_ctor_set(x_167, 5, x_166);
if (x_6 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_168 = lean_ctor_get(x_2, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_2, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_2, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 3);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 4);
lean_inc(x_172);
x_173 = lean_ctor_get(x_2, 5);
lean_inc(x_173);
x_174 = lean_ctor_get(x_2, 6);
lean_inc(x_174);
x_175 = lean_ctor_get(x_2, 7);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_177 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_178 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_179 = lean_ctor_get(x_2, 9);
lean_inc(x_179);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 lean_ctor_release(x_2, 8);
 lean_ctor_release(x_2, 9);
 x_180 = x_2;
} else {
 lean_dec_ref(x_2);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 10, 3);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_168);
lean_ctor_set(x_181, 1, x_169);
lean_ctor_set(x_181, 2, x_170);
lean_ctor_set(x_181, 3, x_171);
lean_ctor_set(x_181, 4, x_172);
lean_ctor_set(x_181, 5, x_173);
lean_ctor_set(x_181, 6, x_174);
lean_ctor_set(x_181, 7, x_175);
lean_ctor_set(x_181, 8, x_165);
lean_ctor_set(x_181, 9, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*10, x_176);
lean_ctor_set_uint8(x_181, sizeof(void*)*10 + 1, x_177);
lean_ctor_set_uint8(x_181, sizeof(void*)*10 + 2, x_178);
x_182 = lean_unsigned_to_nat(0u);
x_183 = l_Lean_Syntax_getArg(x_5, x_182);
x_184 = 0;
lean_inc(x_183);
x_185 = l_Lean_Elab_Term_isLocalTermId_x3f(x_183, x_184, x_181, x_167);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Term_getCurrMacroScope(x_181, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Elab_Term_getMainModule___rarg(x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_195 = l_Lean_addMacroScope(x_192, x_194, x_189);
x_196 = lean_box(0);
x_197 = l_Lean_SourceInfo_inhabited___closed__1;
x_198 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_199 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
lean_ctor_set(x_199, 2, x_195);
lean_ctor_set(x_199, 3, x_196);
x_200 = l_Array_empty___closed__1;
x_201 = lean_array_push(x_200, x_199);
x_202 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_203 = lean_array_push(x_201, x_202);
x_204 = l_Lean_mkTermIdFromIdent___closed__2;
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_203);
x_206 = l_Lean_Syntax_setArg(x_5, x_182, x_205);
x_207 = l_Lean_Syntax_setArg(x_1, x_4, x_206);
x_208 = l_Lean_Elab_Term_getCurrMacroScope(x_181, x_193);
lean_dec(x_181);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = l_Lean_Elab_Term_getMainModule___rarg(x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_214 = x_211;
} else {
 lean_dec_ref(x_211);
 x_214 = lean_box(0);
}
x_215 = l_Lean_addMacroScope(x_212, x_194, x_209);
x_216 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_216, 0, x_197);
lean_ctor_set(x_216, 1, x_198);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set(x_216, 3, x_196);
x_217 = lean_array_push(x_200, x_216);
x_218 = lean_array_push(x_217, x_202);
x_219 = lean_array_push(x_218, x_202);
x_220 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_221 = lean_array_push(x_219, x_220);
x_222 = lean_array_push(x_221, x_183);
x_223 = l_Lean_Parser_Term_letIdDecl___closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_226 = lean_array_push(x_225, x_224);
x_227 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_228 = lean_array_push(x_226, x_227);
x_229 = lean_array_push(x_228, x_207);
x_230 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
if (lean_is_scalar(x_214)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_214;
}
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_213);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_186);
lean_dec(x_183);
lean_dec(x_181);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_185, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_235 = x_185;
} else {
 lean_dec_ref(x_185);
 x_235 = lean_box(0);
}
x_236 = lean_box(0);
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(0, 2, 0);
} else {
 x_237 = x_235;
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_165);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_box(0);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_167);
return x_239;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Source_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
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
lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid structure instance `with` and `..` cannot be used together");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_5);
if (x_8 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_9 = x_68;
goto block_67;
}
else
{
uint8_t x_69; 
x_69 = l_Lean_Syntax_isNone(x_7);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_9 = x_70;
goto block_67;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
block_67:
{
lean_dec(x_9);
if (x_8 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 9);
x_12 = l_Lean_Elab_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_2, 9, x_12);
x_13 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_15 = l_Lean_Elab_Term_throwError___rarg(x_14, x_2, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_5, x_16);
x_18 = 0;
x_19 = l_Lean_Elab_Term_isLocalTermId_x3f(x_17, x_18, x_2, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_5);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_23 = l_unreachable_x21___rarg(x_22);
x_24 = lean_apply_2(x_23, x_2, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_5);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
x_36 = lean_ctor_get(x_2, 3);
x_37 = lean_ctor_get(x_2, 4);
x_38 = lean_ctor_get(x_2, 5);
x_39 = lean_ctor_get(x_2, 6);
x_40 = lean_ctor_get(x_2, 7);
x_41 = lean_ctor_get(x_2, 8);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_45 = lean_ctor_get(x_2, 9);
lean_inc(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_46 = l_Lean_Elab_replaceRef(x_1, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_36);
lean_ctor_set(x_47, 4, x_37);
lean_ctor_set(x_47, 5, x_38);
lean_ctor_set(x_47, 6, x_39);
lean_ctor_set(x_47, 7, x_40);
lean_ctor_set(x_47, 8, x_41);
lean_ctor_set(x_47, 9, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 2, x_44);
x_48 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
x_49 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_50 = l_Lean_Elab_Term_throwError___rarg(x_49, x_47, x_3);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Syntax_getArg(x_5, x_51);
x_53 = 0;
x_54 = l_Lean_Elab_Term_isLocalTermId_x3f(x_52, x_53, x_47, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_5);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_58 = l_unreachable_x21___rarg(x_57);
x_59 = lean_apply_2(x_58, x_47, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_47);
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
x_62 = lean_ctor_get(x_55, 0);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_61)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_61;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_5);
lean_dec(x_2);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_7);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, can't mix field and `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, at most one `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_10, x_11);
x_13 = l_Lean_Syntax_getKind(x_12);
x_14 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_15 = lean_name_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_10);
x_17 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_17;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
x_20 = l_Lean_Syntax_getKind(x_19);
x_21 = lean_name_eq(x_20, x_14);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_10);
x_22 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_25 = l_Lean_Elab_Term_throwErrorAt___rarg(x_10, x_24, x_5, x_6);
lean_dec(x_10);
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
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_10);
x_31 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_31;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_3);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lean_Syntax_getKind(x_33);
x_35 = lean_name_eq(x_34, x_14);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_37 = l_Lean_Elab_Term_throwErrorAt___rarg(x_10, x_36, x_5, x_6);
lean_dec(x_10);
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
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
x_43 = l_Lean_Elab_Term_throwErrorAt___rarg(x_10, x_42, x_5, x_6);
lean_dec(x_10);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_4, x_6, x_8, x_7, x_2, x_3);
lean_dec(x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
x_18 = l_Lean_Syntax_getArg(x_17, x_8);
lean_dec(x_17);
x_19 = l_Lean_Syntax_getKind(x_18);
x_20 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_21 = lean_name_eq(x_19, x_20);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
return x_9;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
x_24 = l_Lean_Syntax_getArg(x_23, x_8);
lean_dec(x_23);
x_25 = l_Lean_Syntax_getKind(x_24);
x_26 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_27 = lean_name_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_7);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_9);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("struct");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("modifyOp");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("s");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Name_toString___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_arrayToExpr___rarg___closed__2;
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n===>\n");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nval: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nSource: ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_2, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
x_10 = l_Lean_Elab_Term_getOptions(x_5, x_6);
if (x_9 == 0)
{
uint8_t x_307; 
x_307 = 0;
x_11 = x_307;
goto block_306;
}
else
{
uint8_t x_308; 
x_308 = 1;
x_11 = x_308;
goto block_306;
}
block_306:
{
lean_object* x_12; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; 
x_295 = lean_ctor_get(x_10, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_10, 1);
lean_inc(x_296);
lean_dec(x_10);
x_297 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_298 = l_Lean_checkTraceOption(x_295, x_297);
lean_dec(x_295);
if (x_298 == 0)
{
x_12 = x_296;
goto block_294;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_inc(x_2);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_2);
x_300 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28;
x_301 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
lean_inc(x_3);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_3);
x_303 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Lean_Elab_Term_logTrace(x_297, x_303, x_5, x_296);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_12 = x_305;
goto block_294;
}
block_294:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_13 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_getMainModule___rarg(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_20 = l_Lean_addMacroScope(x_17, x_19, x_14);
x_21 = lean_box(0);
x_22 = l_Lean_SourceInfo_inhabited___closed__1;
x_23 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_24 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
x_25 = l_Array_empty___closed__1;
x_26 = lean_array_push(x_25, x_24);
x_27 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_28 = lean_array_push(x_26, x_27);
x_29 = l_Lean_mkTermIdFromIdent___closed__2;
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Lean_Syntax_getArg(x_8, x_31);
lean_inc(x_32);
x_33 = l_Lean_Syntax_getKind(x_32);
x_34 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_35 = lean_name_eq(x_33, x_34);
lean_dec(x_33);
x_36 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_37 = lean_array_get_size(x_36);
x_38 = l_Array_extract___rarg(x_36, x_7, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_nullKind;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_Syntax_getArg(x_2, x_31);
x_42 = l_Lean_Syntax_getArg(x_41, x_7);
lean_dec(x_41);
x_43 = l_Lean_Syntax_getArg(x_3, x_31);
x_44 = l_Lean_Elab_Term_getOptions(x_5, x_18);
if (x_35 == 0)
{
lean_object* x_183; 
x_183 = l_Lean_Syntax_getArg(x_32, x_7);
lean_dec(x_32);
x_45 = x_183;
goto block_182;
}
else
{
x_45 = x_32;
goto block_182;
}
block_182:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = l_Lean_Syntax_setArg(x_2, x_31, x_45);
x_47 = l_Lean_Syntax_setArg(x_46, x_7, x_40);
x_48 = l_Lean_mkOptionalNode___closed__2;
x_49 = lean_array_push(x_48, x_47);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_3);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_3, 1);
x_168 = lean_array_get_size(x_167);
x_169 = lean_nat_dec_lt(x_31, x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_dec(x_30);
x_51 = x_3;
goto block_165;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_box(0);
x_171 = lean_array_fset(x_167, x_31, x_170);
x_172 = lean_array_fset(x_171, x_31, x_30);
lean_ctor_set(x_3, 1, x_172);
x_51 = x_3;
goto block_165;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_3, 0);
x_174 = lean_ctor_get(x_3, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_3);
x_175 = lean_array_get_size(x_174);
x_176 = lean_nat_dec_lt(x_31, x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_30);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
x_51 = x_177;
goto block_165;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_box(0);
x_179 = lean_array_fset(x_174, x_31, x_178);
x_180 = lean_array_fset(x_179, x_31, x_30);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
x_51 = x_181;
goto block_165;
}
}
}
else
{
lean_dec(x_30);
x_51 = x_3;
goto block_165;
}
block_165:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
lean_inc(x_1);
x_52 = l_Lean_Syntax_setArg(x_1, x_7, x_51);
x_53 = lean_unsigned_to_nat(2u);
x_54 = l_Lean_Syntax_setArg(x_52, x_53, x_50);
x_154 = lean_ctor_get(x_44, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_44, 1);
lean_inc(x_155);
lean_dec(x_44);
x_156 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_157 = l_Lean_checkTraceOption(x_154, x_156);
lean_dec(x_154);
if (x_157 == 0)
{
x_55 = x_155;
goto block_153;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_inc(x_1);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_1);
x_159 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
x_160 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_inc(x_54);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_54);
x_162 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_Elab_Term_logTrace(x_156, x_162, x_5, x_155);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_55 = x_164;
goto block_153;
}
block_153:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_56 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_getMainModule___rarg(x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_array_push(x_25, x_43);
x_63 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_64 = lean_array_push(x_62, x_63);
x_65 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_inc(x_57);
lean_inc(x_60);
x_66 = l_Lean_addMacroScope(x_60, x_65, x_57);
x_67 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
x_68 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_22);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_array_push(x_64, x_69);
x_71 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_25, x_72);
x_74 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_inc(x_57);
lean_inc(x_60);
x_75 = l_Lean_addMacroScope(x_60, x_74, x_57);
x_76 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_22);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_21);
x_78 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_79 = lean_array_push(x_78, x_77);
x_80 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_81 = lean_array_push(x_79, x_80);
x_82 = lean_array_push(x_81, x_42);
x_83 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_84 = lean_array_push(x_82, x_83);
x_85 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_25, x_86);
x_88 = l_Lean_addMacroScope(x_60, x_19, x_57);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_22);
lean_ctor_set(x_89, 1, x_23);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_21);
x_90 = lean_array_push(x_25, x_89);
x_91 = lean_array_push(x_90, x_27);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_29);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_push(x_25, x_92);
x_94 = l_Lean_nullKind___closed__2;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_97 = lean_array_push(x_96, x_95);
x_98 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_99 = lean_array_push(x_97, x_98);
x_100 = lean_array_push(x_99, x_54);
x_101 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_array_push(x_25, x_102);
x_104 = lean_array_push(x_103, x_27);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_array_push(x_78, x_105);
x_107 = lean_array_push(x_106, x_83);
x_108 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_array_push(x_87, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_73, x_111);
x_113 = l_Lean_mkAppStx___closed__8;
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_141 = l_Lean_Elab_Term_getOptions(x_5, x_61);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_145 = l_Lean_checkTraceOption(x_142, x_144);
lean_dec(x_142);
if (x_145 == 0)
{
x_115 = x_143;
goto block_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc(x_1);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_1);
x_147 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_148 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
lean_inc(x_114);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_114);
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_Elab_Term_logTrace(x_144, x_150, x_5, x_143);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_115 = x_152;
goto block_140;
}
block_140:
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_5);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_5, 7);
lean_inc(x_114);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_114);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_5, 7, x_119);
x_120 = 1;
x_121 = l_Lean_Elab_Term_elabTerm(x_114, x_4, x_120, x_5, x_115);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; 
x_122 = lean_ctor_get(x_5, 0);
x_123 = lean_ctor_get(x_5, 1);
x_124 = lean_ctor_get(x_5, 2);
x_125 = lean_ctor_get(x_5, 3);
x_126 = lean_ctor_get(x_5, 4);
x_127 = lean_ctor_get(x_5, 5);
x_128 = lean_ctor_get(x_5, 6);
x_129 = lean_ctor_get(x_5, 7);
x_130 = lean_ctor_get(x_5, 8);
x_131 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_132 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_133 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_134 = lean_ctor_get(x_5, 9);
lean_inc(x_134);
lean_inc(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_5);
lean_inc(x_114);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_114);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_129);
x_137 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_137, 0, x_122);
lean_ctor_set(x_137, 1, x_123);
lean_ctor_set(x_137, 2, x_124);
lean_ctor_set(x_137, 3, x_125);
lean_ctor_set(x_137, 4, x_126);
lean_ctor_set(x_137, 5, x_127);
lean_ctor_set(x_137, 6, x_128);
lean_ctor_set(x_137, 7, x_136);
lean_ctor_set(x_137, 8, x_130);
lean_ctor_set(x_137, 9, x_134);
lean_ctor_set_uint8(x_137, sizeof(void*)*10, x_131);
lean_ctor_set_uint8(x_137, sizeof(void*)*10 + 1, x_132);
lean_ctor_set_uint8(x_137, sizeof(void*)*10 + 2, x_133);
x_138 = 1;
x_139 = l_Lean_Elab_Term_elabTerm(x_114, x_4, x_138, x_137, x_115);
return x_139;
}
}
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; 
lean_dec(x_8);
x_184 = lean_unsigned_to_nat(3u);
x_185 = l_Lean_Syntax_getArg(x_2, x_184);
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Lean_Syntax_getArg(x_2, x_186);
lean_dec(x_2);
x_188 = l_Lean_Syntax_getArg(x_187, x_7);
lean_dec(x_187);
x_189 = l_Lean_Syntax_getArg(x_3, x_186);
lean_dec(x_3);
x_190 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_12);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Elab_Term_getMainModule___rarg(x_192);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Array_empty___closed__1;
x_197 = lean_array_push(x_196, x_189);
x_198 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_199 = lean_array_push(x_197, x_198);
x_200 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_inc(x_191);
lean_inc(x_194);
x_201 = l_Lean_addMacroScope(x_194, x_200, x_191);
x_202 = lean_box(0);
x_203 = l_Lean_SourceInfo_inhabited___closed__1;
x_204 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
x_205 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
x_206 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
lean_ctor_set(x_206, 2, x_201);
lean_ctor_set(x_206, 3, x_205);
x_207 = lean_array_push(x_199, x_206);
x_208 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_array_push(x_196, x_209);
x_211 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_inc(x_191);
lean_inc(x_194);
x_212 = l_Lean_addMacroScope(x_194, x_211, x_191);
x_213 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_214 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_214, 0, x_203);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_214, 2, x_212);
lean_ctor_set(x_214, 3, x_202);
x_215 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_216 = lean_array_push(x_215, x_214);
x_217 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_218 = lean_array_push(x_216, x_217);
x_219 = lean_array_push(x_218, x_188);
x_220 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_221 = lean_array_push(x_219, x_220);
x_222 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = lean_array_push(x_196, x_223);
x_225 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_226 = l_Lean_addMacroScope(x_194, x_225, x_191);
x_227 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_228 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_228, 0, x_203);
lean_ctor_set(x_228, 1, x_227);
lean_ctor_set(x_228, 2, x_226);
lean_ctor_set(x_228, 3, x_202);
x_229 = lean_array_push(x_196, x_228);
x_230 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_231 = lean_array_push(x_229, x_230);
x_232 = l_Lean_mkTermIdFromIdent___closed__2;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_array_push(x_196, x_233);
x_235 = l_Lean_nullKind___closed__2;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_238 = lean_array_push(x_237, x_236);
x_239 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_240 = lean_array_push(x_238, x_239);
x_241 = lean_array_push(x_240, x_185);
x_242 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_array_push(x_196, x_243);
x_245 = lean_array_push(x_244, x_230);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_235);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_array_push(x_215, x_246);
x_248 = lean_array_push(x_247, x_220);
x_249 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_248);
x_251 = lean_array_push(x_224, x_250);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_235);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_array_push(x_210, x_252);
x_254 = l_Lean_mkAppStx___closed__8;
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_253);
x_282 = l_Lean_Elab_Term_getOptions(x_5, x_195);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_286 = l_Lean_checkTraceOption(x_283, x_285);
lean_dec(x_283);
if (x_286 == 0)
{
x_256 = x_284;
goto block_281;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_inc(x_1);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_1);
x_288 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_289 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
lean_inc(x_255);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_255);
x_291 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = l_Lean_Elab_Term_logTrace(x_285, x_291, x_5, x_284);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_256 = x_293;
goto block_281;
}
block_281:
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_5);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; 
x_258 = lean_ctor_get(x_5, 7);
lean_inc(x_255);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_255);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set(x_5, 7, x_260);
x_261 = 1;
x_262 = l_Lean_Elab_Term_elabTerm(x_255, x_4, x_261, x_5, x_256);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; 
x_263 = lean_ctor_get(x_5, 0);
x_264 = lean_ctor_get(x_5, 1);
x_265 = lean_ctor_get(x_5, 2);
x_266 = lean_ctor_get(x_5, 3);
x_267 = lean_ctor_get(x_5, 4);
x_268 = lean_ctor_get(x_5, 5);
x_269 = lean_ctor_get(x_5, 6);
x_270 = lean_ctor_get(x_5, 7);
x_271 = lean_ctor_get(x_5, 8);
x_272 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_273 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_274 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_275 = lean_ctor_get(x_5, 9);
lean_inc(x_275);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_5);
lean_inc(x_255);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_255);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_270);
x_278 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_278, 0, x_263);
lean_ctor_set(x_278, 1, x_264);
lean_ctor_set(x_278, 2, x_265);
lean_ctor_set(x_278, 3, x_266);
lean_ctor_set(x_278, 4, x_267);
lean_ctor_set(x_278, 5, x_268);
lean_ctor_set(x_278, 6, x_269);
lean_ctor_set(x_278, 7, x_277);
lean_ctor_set(x_278, 8, x_271);
lean_ctor_set(x_278, 9, x_275);
lean_ctor_set_uint8(x_278, sizeof(void*)*10, x_272);
lean_ctor_set_uint8(x_278, sizeof(void*)*10 + 1, x_273);
lean_ctor_set_uint8(x_278, sizeof(void*)*10 + 2, x_274);
x_279 = 1;
x_280 = l_Lean_Elab_Term_elabTerm(x_255, x_4, x_279, x_278, x_256);
return x_280;
}
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, expected type is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, source type is not of the form (C ...)");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
lean_inc(x_3);
x_24 = l_Lean_Elab_Term_inferType(x_23, x_3, x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_3);
x_27 = l_Lean_Elab_Term_whnf(x_25, x_3, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn___main(x_28);
x_31 = l_Lean_Elab_Term_tryPostponeIfMVar(x_28, x_3, x_29);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 1);
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_3);
x_42 = lean_ctor_get(x_30, 0);
lean_inc(x_42);
lean_dec(x_30);
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
else
{
lean_object* x_43; 
lean_free_object(x_31);
lean_dec(x_30);
x_43 = lean_box(0);
x_35 = x_43;
goto block_41;
}
block_41:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_28);
x_37 = l_Lean_indentExpr(x_36);
x_38 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Term_throwError___rarg(x_39, x_3, x_33);
return x_40;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_dec(x_31);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_28);
lean_dec(x_3);
x_52 = lean_ctor_get(x_30, 0);
lean_inc(x_52);
lean_dec(x_30);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_44);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec(x_30);
x_54 = lean_box(0);
x_45 = x_54;
goto block_51;
}
block_51:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_45);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_28);
x_47 = l_Lean_indentExpr(x_46);
x_48 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_Term_throwError___rarg(x_49, x_3, x_44);
return x_50;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_3);
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
else
{
uint8_t x_63; 
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
return x_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_24, 0);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_24);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_dec(x_2);
x_67 = lean_box(0);
x_7 = x_67;
goto block_22;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_68);
x_69 = l_Lean_Elab_Term_whnf(x_68, x_3, x_6);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_80; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_80 = l_Lean_Expr_getAppFn___main(x_71);
lean_dec(x_71);
switch (lean_obj_tag(x_80)) {
case 0:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
x_81 = lean_ctor_get(x_2, 1);
lean_inc(x_81);
lean_dec(x_2);
lean_inc(x_3);
x_82 = l_Lean_Elab_Term_inferType(x_81, x_3, x_72);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_3);
x_85 = l_Lean_Elab_Term_whnf(x_83, x_3, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Expr_getAppFn___main(x_86);
x_89 = l_Lean_Elab_Term_tryPostponeIfMVar(x_86, x_3, x_87);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
if (lean_obj_tag(x_88) == 4)
{
lean_object* x_100; 
lean_dec(x_86);
lean_dec(x_3);
x_100 = lean_ctor_get(x_88, 0);
lean_inc(x_100);
lean_dec(x_88);
lean_ctor_set(x_89, 0, x_100);
return x_89;
}
else
{
lean_object* x_101; 
lean_free_object(x_89);
lean_dec(x_88);
x_101 = lean_box(0);
x_93 = x_101;
goto block_99;
}
block_99:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_86);
x_95 = l_Lean_indentExpr(x_94);
x_96 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_98 = l_Lean_Elab_Term_throwError___rarg(x_97, x_3, x_91);
return x_98;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
lean_dec(x_89);
if (lean_obj_tag(x_88) == 4)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_86);
lean_dec(x_3);
x_110 = lean_ctor_get(x_88, 0);
lean_inc(x_110);
lean_dec(x_88);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_88);
x_112 = lean_box(0);
x_103 = x_112;
goto block_109;
}
block_109:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_103);
x_104 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_104, 0, x_86);
x_105 = l_Lean_indentExpr(x_104);
x_106 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_107 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = l_Lean_Elab_Term_throwError___rarg(x_107, x_3, x_102);
return x_108;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_89);
if (x_113 == 0)
{
return x_89;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_89, 0);
x_115 = lean_ctor_get(x_89, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_89);
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
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_85);
if (x_117 == 0)
{
return x_85;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_85, 0);
x_119 = lean_ctor_get(x_85, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_85);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_82);
if (x_121 == 0)
{
return x_82;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_82, 0);
x_123 = lean_ctor_get(x_82, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_82);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_2);
x_125 = lean_box(0);
x_73 = x_125;
goto block_79;
}
}
case 1:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_68);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_dec(x_2);
lean_inc(x_3);
x_127 = l_Lean_Elab_Term_inferType(x_126, x_3, x_72);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_3);
x_130 = l_Lean_Elab_Term_whnf(x_128, x_3, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Expr_getAppFn___main(x_131);
x_134 = l_Lean_Elab_Term_tryPostponeIfMVar(x_131, x_3, x_132);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_134, 1);
x_137 = lean_ctor_get(x_134, 0);
lean_dec(x_137);
if (lean_obj_tag(x_133) == 4)
{
lean_object* x_145; 
lean_dec(x_131);
lean_dec(x_3);
x_145 = lean_ctor_get(x_133, 0);
lean_inc(x_145);
lean_dec(x_133);
lean_ctor_set(x_134, 0, x_145);
return x_134;
}
else
{
lean_object* x_146; 
lean_free_object(x_134);
lean_dec(x_133);
x_146 = lean_box(0);
x_138 = x_146;
goto block_144;
}
block_144:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_138);
x_139 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_139, 0, x_131);
x_140 = l_Lean_indentExpr(x_139);
x_141 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_142 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = l_Lean_Elab_Term_throwError___rarg(x_142, x_3, x_136);
return x_143;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
lean_dec(x_134);
if (lean_obj_tag(x_133) == 4)
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_131);
lean_dec(x_3);
x_155 = lean_ctor_get(x_133, 0);
lean_inc(x_155);
lean_dec(x_133);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_147);
return x_156;
}
else
{
lean_object* x_157; 
lean_dec(x_133);
x_157 = lean_box(0);
x_148 = x_157;
goto block_154;
}
block_154:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_148);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_131);
x_150 = l_Lean_indentExpr(x_149);
x_151 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_152 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Lean_Elab_Term_throwError___rarg(x_152, x_3, x_147);
return x_153;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_3);
x_158 = !lean_is_exclusive(x_134);
if (x_158 == 0)
{
return x_134;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_134, 0);
x_160 = lean_ctor_get(x_134, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_134);
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
lean_dec(x_3);
x_162 = !lean_is_exclusive(x_130);
if (x_162 == 0)
{
return x_130;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_130, 0);
x_164 = lean_ctor_get(x_130, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_130);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_3);
x_166 = !lean_is_exclusive(x_127);
if (x_166 == 0)
{
return x_127;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_127, 0);
x_168 = lean_ctor_get(x_127, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_127);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
lean_object* x_170; 
lean_dec(x_2);
x_170 = lean_box(0);
x_73 = x_170;
goto block_79;
}
}
case 2:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_68);
x_171 = lean_ctor_get(x_2, 1);
lean_inc(x_171);
lean_dec(x_2);
lean_inc(x_3);
x_172 = l_Lean_Elab_Term_inferType(x_171, x_3, x_72);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_3);
x_175 = l_Lean_Elab_Term_whnf(x_173, x_3, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l_Lean_Expr_getAppFn___main(x_176);
x_179 = l_Lean_Elab_Term_tryPostponeIfMVar(x_176, x_3, x_177);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_179, 1);
x_182 = lean_ctor_get(x_179, 0);
lean_dec(x_182);
if (lean_obj_tag(x_178) == 4)
{
lean_object* x_190; 
lean_dec(x_176);
lean_dec(x_3);
x_190 = lean_ctor_get(x_178, 0);
lean_inc(x_190);
lean_dec(x_178);
lean_ctor_set(x_179, 0, x_190);
return x_179;
}
else
{
lean_object* x_191; 
lean_free_object(x_179);
lean_dec(x_178);
x_191 = lean_box(0);
x_183 = x_191;
goto block_189;
}
block_189:
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_183);
x_184 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_184, 0, x_176);
x_185 = l_Lean_indentExpr(x_184);
x_186 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_187 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_185);
x_188 = l_Lean_Elab_Term_throwError___rarg(x_187, x_3, x_181);
return x_188;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_179, 1);
lean_inc(x_192);
lean_dec(x_179);
if (lean_obj_tag(x_178) == 4)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_176);
lean_dec(x_3);
x_200 = lean_ctor_get(x_178, 0);
lean_inc(x_200);
lean_dec(x_178);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_192);
return x_201;
}
else
{
lean_object* x_202; 
lean_dec(x_178);
x_202 = lean_box(0);
x_193 = x_202;
goto block_199;
}
block_199:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_193);
x_194 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_194, 0, x_176);
x_195 = l_Lean_indentExpr(x_194);
x_196 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_197 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_195);
x_198 = l_Lean_Elab_Term_throwError___rarg(x_197, x_3, x_192);
return x_198;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_3);
x_203 = !lean_is_exclusive(x_179);
if (x_203 == 0)
{
return x_179;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_179, 0);
x_205 = lean_ctor_get(x_179, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_179);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_3);
x_207 = !lean_is_exclusive(x_175);
if (x_207 == 0)
{
return x_175;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_175, 0);
x_209 = lean_ctor_get(x_175, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_175);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_3);
x_211 = !lean_is_exclusive(x_172);
if (x_211 == 0)
{
return x_172;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_172, 0);
x_213 = lean_ctor_get(x_172, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_172);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; 
lean_dec(x_2);
x_215 = lean_box(0);
x_73 = x_215;
goto block_79;
}
}
case 3:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_68);
x_216 = lean_ctor_get(x_2, 1);
lean_inc(x_216);
lean_dec(x_2);
lean_inc(x_3);
x_217 = l_Lean_Elab_Term_inferType(x_216, x_3, x_72);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_3);
x_220 = l_Lean_Elab_Term_whnf(x_218, x_3, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_Expr_getAppFn___main(x_221);
x_224 = l_Lean_Elab_Term_tryPostponeIfMVar(x_221, x_3, x_222);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_224);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_224, 1);
x_227 = lean_ctor_get(x_224, 0);
lean_dec(x_227);
if (lean_obj_tag(x_223) == 4)
{
lean_object* x_235; 
lean_dec(x_221);
lean_dec(x_3);
x_235 = lean_ctor_get(x_223, 0);
lean_inc(x_235);
lean_dec(x_223);
lean_ctor_set(x_224, 0, x_235);
return x_224;
}
else
{
lean_object* x_236; 
lean_free_object(x_224);
lean_dec(x_223);
x_236 = lean_box(0);
x_228 = x_236;
goto block_234;
}
block_234:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_228);
x_229 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_229, 0, x_221);
x_230 = l_Lean_indentExpr(x_229);
x_231 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = l_Lean_Elab_Term_throwError___rarg(x_232, x_3, x_226);
return x_233;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_224, 1);
lean_inc(x_237);
lean_dec(x_224);
if (lean_obj_tag(x_223) == 4)
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_221);
lean_dec(x_3);
x_245 = lean_ctor_get(x_223, 0);
lean_inc(x_245);
lean_dec(x_223);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_237);
return x_246;
}
else
{
lean_object* x_247; 
lean_dec(x_223);
x_247 = lean_box(0);
x_238 = x_247;
goto block_244;
}
block_244:
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_238);
x_239 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_239, 0, x_221);
x_240 = l_Lean_indentExpr(x_239);
x_241 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_242 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_240);
x_243 = l_Lean_Elab_Term_throwError___rarg(x_242, x_3, x_237);
return x_243;
}
}
}
else
{
uint8_t x_248; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_3);
x_248 = !lean_is_exclusive(x_224);
if (x_248 == 0)
{
return x_224;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_224, 0);
x_250 = lean_ctor_get(x_224, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_224);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
else
{
uint8_t x_252; 
lean_dec(x_3);
x_252 = !lean_is_exclusive(x_220);
if (x_252 == 0)
{
return x_220;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_220, 0);
x_254 = lean_ctor_get(x_220, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_220);
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
lean_dec(x_3);
x_256 = !lean_is_exclusive(x_217);
if (x_256 == 0)
{
return x_217;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_217, 0);
x_258 = lean_ctor_get(x_217, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_217);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
lean_object* x_260; 
lean_dec(x_2);
x_260 = lean_box(0);
x_73 = x_260;
goto block_79;
}
}
case 4:
{
lean_object* x_261; 
lean_dec(x_68);
lean_dec(x_3);
lean_dec(x_2);
x_261 = lean_ctor_get(x_80, 0);
lean_inc(x_261);
lean_dec(x_80);
lean_ctor_set(x_69, 0, x_261);
return x_69;
}
case 5:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_68);
x_262 = lean_ctor_get(x_2, 1);
lean_inc(x_262);
lean_dec(x_2);
lean_inc(x_3);
x_263 = l_Lean_Elab_Term_inferType(x_262, x_3, x_72);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_3);
x_266 = l_Lean_Elab_Term_whnf(x_264, x_3, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l_Lean_Expr_getAppFn___main(x_267);
x_270 = l_Lean_Elab_Term_tryPostponeIfMVar(x_267, x_3, x_268);
if (lean_obj_tag(x_270) == 0)
{
uint8_t x_271; 
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 1);
x_273 = lean_ctor_get(x_270, 0);
lean_dec(x_273);
if (lean_obj_tag(x_269) == 4)
{
lean_object* x_281; 
lean_dec(x_267);
lean_dec(x_3);
x_281 = lean_ctor_get(x_269, 0);
lean_inc(x_281);
lean_dec(x_269);
lean_ctor_set(x_270, 0, x_281);
return x_270;
}
else
{
lean_object* x_282; 
lean_free_object(x_270);
lean_dec(x_269);
x_282 = lean_box(0);
x_274 = x_282;
goto block_280;
}
block_280:
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_274);
x_275 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_275, 0, x_267);
x_276 = l_Lean_indentExpr(x_275);
x_277 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_278 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
x_279 = l_Lean_Elab_Term_throwError___rarg(x_278, x_3, x_272);
return x_279;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_270, 1);
lean_inc(x_283);
lean_dec(x_270);
if (lean_obj_tag(x_269) == 4)
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_267);
lean_dec(x_3);
x_291 = lean_ctor_get(x_269, 0);
lean_inc(x_291);
lean_dec(x_269);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_283);
return x_292;
}
else
{
lean_object* x_293; 
lean_dec(x_269);
x_293 = lean_box(0);
x_284 = x_293;
goto block_290;
}
block_290:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_284);
x_285 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_285, 0, x_267);
x_286 = l_Lean_indentExpr(x_285);
x_287 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_288 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = l_Lean_Elab_Term_throwError___rarg(x_288, x_3, x_283);
return x_289;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_3);
x_294 = !lean_is_exclusive(x_270);
if (x_294 == 0)
{
return x_270;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_270, 0);
x_296 = lean_ctor_get(x_270, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_270);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_3);
x_298 = !lean_is_exclusive(x_266);
if (x_298 == 0)
{
return x_266;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_266, 0);
x_300 = lean_ctor_get(x_266, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_266);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_3);
x_302 = !lean_is_exclusive(x_263);
if (x_302 == 0)
{
return x_263;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_263, 0);
x_304 = lean_ctor_get(x_263, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_263);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
lean_object* x_306; 
lean_dec(x_2);
x_306 = lean_box(0);
x_73 = x_306;
goto block_79;
}
}
case 6:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_307; lean_object* x_308; 
lean_dec(x_68);
x_307 = lean_ctor_get(x_2, 1);
lean_inc(x_307);
lean_dec(x_2);
lean_inc(x_3);
x_308 = l_Lean_Elab_Term_inferType(x_307, x_3, x_72);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
lean_inc(x_3);
x_311 = l_Lean_Elab_Term_whnf(x_309, x_3, x_310);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_311, 1);
lean_inc(x_313);
lean_dec(x_311);
x_314 = l_Lean_Expr_getAppFn___main(x_312);
x_315 = l_Lean_Elab_Term_tryPostponeIfMVar(x_312, x_3, x_313);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_315, 1);
x_318 = lean_ctor_get(x_315, 0);
lean_dec(x_318);
if (lean_obj_tag(x_314) == 4)
{
lean_object* x_326; 
lean_dec(x_312);
lean_dec(x_3);
x_326 = lean_ctor_get(x_314, 0);
lean_inc(x_326);
lean_dec(x_314);
lean_ctor_set(x_315, 0, x_326);
return x_315;
}
else
{
lean_object* x_327; 
lean_free_object(x_315);
lean_dec(x_314);
x_327 = lean_box(0);
x_319 = x_327;
goto block_325;
}
block_325:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_319);
x_320 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_320, 0, x_312);
x_321 = l_Lean_indentExpr(x_320);
x_322 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_323 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_321);
x_324 = l_Lean_Elab_Term_throwError___rarg(x_323, x_3, x_317);
return x_324;
}
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_315, 1);
lean_inc(x_328);
lean_dec(x_315);
if (lean_obj_tag(x_314) == 4)
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_312);
lean_dec(x_3);
x_336 = lean_ctor_get(x_314, 0);
lean_inc(x_336);
lean_dec(x_314);
x_337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set(x_337, 1, x_328);
return x_337;
}
else
{
lean_object* x_338; 
lean_dec(x_314);
x_338 = lean_box(0);
x_329 = x_338;
goto block_335;
}
block_335:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_329);
x_330 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_330, 0, x_312);
x_331 = l_Lean_indentExpr(x_330);
x_332 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_333 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
x_334 = l_Lean_Elab_Term_throwError___rarg(x_333, x_3, x_328);
return x_334;
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_314);
lean_dec(x_312);
lean_dec(x_3);
x_339 = !lean_is_exclusive(x_315);
if (x_339 == 0)
{
return x_315;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_315, 0);
x_341 = lean_ctor_get(x_315, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_315);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
uint8_t x_343; 
lean_dec(x_3);
x_343 = !lean_is_exclusive(x_311);
if (x_343 == 0)
{
return x_311;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_311, 0);
x_345 = lean_ctor_get(x_311, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_311);
x_346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
return x_346;
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_3);
x_347 = !lean_is_exclusive(x_308);
if (x_347 == 0)
{
return x_308;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_308, 0);
x_349 = lean_ctor_get(x_308, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_308);
x_350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; 
lean_dec(x_2);
x_351 = lean_box(0);
x_73 = x_351;
goto block_79;
}
}
case 7:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_68);
x_352 = lean_ctor_get(x_2, 1);
lean_inc(x_352);
lean_dec(x_2);
lean_inc(x_3);
x_353 = l_Lean_Elab_Term_inferType(x_352, x_3, x_72);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
lean_inc(x_3);
x_356 = l_Lean_Elab_Term_whnf(x_354, x_3, x_355);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = l_Lean_Expr_getAppFn___main(x_357);
x_360 = l_Lean_Elab_Term_tryPostponeIfMVar(x_357, x_3, x_358);
if (lean_obj_tag(x_360) == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_360, 1);
x_363 = lean_ctor_get(x_360, 0);
lean_dec(x_363);
if (lean_obj_tag(x_359) == 4)
{
lean_object* x_371; 
lean_dec(x_357);
lean_dec(x_3);
x_371 = lean_ctor_get(x_359, 0);
lean_inc(x_371);
lean_dec(x_359);
lean_ctor_set(x_360, 0, x_371);
return x_360;
}
else
{
lean_object* x_372; 
lean_free_object(x_360);
lean_dec(x_359);
x_372 = lean_box(0);
x_364 = x_372;
goto block_370;
}
block_370:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_364);
x_365 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_365, 0, x_357);
x_366 = l_Lean_indentExpr(x_365);
x_367 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_368 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = l_Lean_Elab_Term_throwError___rarg(x_368, x_3, x_362);
return x_369;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_360, 1);
lean_inc(x_373);
lean_dec(x_360);
if (lean_obj_tag(x_359) == 4)
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_357);
lean_dec(x_3);
x_381 = lean_ctor_get(x_359, 0);
lean_inc(x_381);
lean_dec(x_359);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_373);
return x_382;
}
else
{
lean_object* x_383; 
lean_dec(x_359);
x_383 = lean_box(0);
x_374 = x_383;
goto block_380;
}
block_380:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_374);
x_375 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_375, 0, x_357);
x_376 = l_Lean_indentExpr(x_375);
x_377 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_378 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Elab_Term_throwError___rarg(x_378, x_3, x_373);
return x_379;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_359);
lean_dec(x_357);
lean_dec(x_3);
x_384 = !lean_is_exclusive(x_360);
if (x_384 == 0)
{
return x_360;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_360, 0);
x_386 = lean_ctor_get(x_360, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_360);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
else
{
uint8_t x_388; 
lean_dec(x_3);
x_388 = !lean_is_exclusive(x_356);
if (x_388 == 0)
{
return x_356;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_356, 0);
x_390 = lean_ctor_get(x_356, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_356);
x_391 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
return x_391;
}
}
}
else
{
uint8_t x_392; 
lean_dec(x_3);
x_392 = !lean_is_exclusive(x_353);
if (x_392 == 0)
{
return x_353;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_353, 0);
x_394 = lean_ctor_get(x_353, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_353);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
lean_object* x_396; 
lean_dec(x_2);
x_396 = lean_box(0);
x_73 = x_396;
goto block_79;
}
}
case 8:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_68);
x_397 = lean_ctor_get(x_2, 1);
lean_inc(x_397);
lean_dec(x_2);
lean_inc(x_3);
x_398 = l_Lean_Elab_Term_inferType(x_397, x_3, x_72);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
lean_inc(x_3);
x_401 = l_Lean_Elab_Term_whnf(x_399, x_3, x_400);
if (lean_obj_tag(x_401) == 0)
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_401, 1);
lean_inc(x_403);
lean_dec(x_401);
x_404 = l_Lean_Expr_getAppFn___main(x_402);
x_405 = l_Lean_Elab_Term_tryPostponeIfMVar(x_402, x_3, x_403);
if (lean_obj_tag(x_405) == 0)
{
uint8_t x_406; 
x_406 = !lean_is_exclusive(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_405, 1);
x_408 = lean_ctor_get(x_405, 0);
lean_dec(x_408);
if (lean_obj_tag(x_404) == 4)
{
lean_object* x_416; 
lean_dec(x_402);
lean_dec(x_3);
x_416 = lean_ctor_get(x_404, 0);
lean_inc(x_416);
lean_dec(x_404);
lean_ctor_set(x_405, 0, x_416);
return x_405;
}
else
{
lean_object* x_417; 
lean_free_object(x_405);
lean_dec(x_404);
x_417 = lean_box(0);
x_409 = x_417;
goto block_415;
}
block_415:
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_409);
x_410 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_410, 0, x_402);
x_411 = l_Lean_indentExpr(x_410);
x_412 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_413 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_411);
x_414 = l_Lean_Elab_Term_throwError___rarg(x_413, x_3, x_407);
return x_414;
}
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_405, 1);
lean_inc(x_418);
lean_dec(x_405);
if (lean_obj_tag(x_404) == 4)
{
lean_object* x_426; lean_object* x_427; 
lean_dec(x_402);
lean_dec(x_3);
x_426 = lean_ctor_get(x_404, 0);
lean_inc(x_426);
lean_dec(x_404);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_418);
return x_427;
}
else
{
lean_object* x_428; 
lean_dec(x_404);
x_428 = lean_box(0);
x_419 = x_428;
goto block_425;
}
block_425:
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_419);
x_420 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_420, 0, x_402);
x_421 = l_Lean_indentExpr(x_420);
x_422 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_423 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = l_Lean_Elab_Term_throwError___rarg(x_423, x_3, x_418);
return x_424;
}
}
}
else
{
uint8_t x_429; 
lean_dec(x_404);
lean_dec(x_402);
lean_dec(x_3);
x_429 = !lean_is_exclusive(x_405);
if (x_429 == 0)
{
return x_405;
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_405, 0);
x_431 = lean_ctor_get(x_405, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_405);
x_432 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
return x_432;
}
}
}
else
{
uint8_t x_433; 
lean_dec(x_3);
x_433 = !lean_is_exclusive(x_401);
if (x_433 == 0)
{
return x_401;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_401, 0);
x_435 = lean_ctor_get(x_401, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_401);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_3);
x_437 = !lean_is_exclusive(x_398);
if (x_437 == 0)
{
return x_398;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_398, 0);
x_439 = lean_ctor_get(x_398, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_398);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
else
{
lean_object* x_441; 
lean_dec(x_2);
x_441 = lean_box(0);
x_73 = x_441;
goto block_79;
}
}
case 9:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_68);
x_442 = lean_ctor_get(x_2, 1);
lean_inc(x_442);
lean_dec(x_2);
lean_inc(x_3);
x_443 = l_Lean_Elab_Term_inferType(x_442, x_3, x_72);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_443, 1);
lean_inc(x_445);
lean_dec(x_443);
lean_inc(x_3);
x_446 = l_Lean_Elab_Term_whnf(x_444, x_3, x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_447 = lean_ctor_get(x_446, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_446, 1);
lean_inc(x_448);
lean_dec(x_446);
x_449 = l_Lean_Expr_getAppFn___main(x_447);
x_450 = l_Lean_Elab_Term_tryPostponeIfMVar(x_447, x_3, x_448);
if (lean_obj_tag(x_450) == 0)
{
uint8_t x_451; 
x_451 = !lean_is_exclusive(x_450);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_452 = lean_ctor_get(x_450, 1);
x_453 = lean_ctor_get(x_450, 0);
lean_dec(x_453);
if (lean_obj_tag(x_449) == 4)
{
lean_object* x_461; 
lean_dec(x_447);
lean_dec(x_3);
x_461 = lean_ctor_get(x_449, 0);
lean_inc(x_461);
lean_dec(x_449);
lean_ctor_set(x_450, 0, x_461);
return x_450;
}
else
{
lean_object* x_462; 
lean_free_object(x_450);
lean_dec(x_449);
x_462 = lean_box(0);
x_454 = x_462;
goto block_460;
}
block_460:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_454);
x_455 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_455, 0, x_447);
x_456 = l_Lean_indentExpr(x_455);
x_457 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_458 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_456);
x_459 = l_Lean_Elab_Term_throwError___rarg(x_458, x_3, x_452);
return x_459;
}
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_450, 1);
lean_inc(x_463);
lean_dec(x_450);
if (lean_obj_tag(x_449) == 4)
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_447);
lean_dec(x_3);
x_471 = lean_ctor_get(x_449, 0);
lean_inc(x_471);
lean_dec(x_449);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_463);
return x_472;
}
else
{
lean_object* x_473; 
lean_dec(x_449);
x_473 = lean_box(0);
x_464 = x_473;
goto block_470;
}
block_470:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_464);
x_465 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_465, 0, x_447);
x_466 = l_Lean_indentExpr(x_465);
x_467 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_468 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_466);
x_469 = l_Lean_Elab_Term_throwError___rarg(x_468, x_3, x_463);
return x_469;
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_3);
x_474 = !lean_is_exclusive(x_450);
if (x_474 == 0)
{
return x_450;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_450, 0);
x_476 = lean_ctor_get(x_450, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_450);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_3);
x_478 = !lean_is_exclusive(x_446);
if (x_478 == 0)
{
return x_446;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_446, 0);
x_480 = lean_ctor_get(x_446, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_446);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_3);
x_482 = !lean_is_exclusive(x_443);
if (x_482 == 0)
{
return x_443;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_443, 0);
x_484 = lean_ctor_get(x_443, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_443);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
lean_object* x_486; 
lean_dec(x_2);
x_486 = lean_box(0);
x_73 = x_486;
goto block_79;
}
}
case 10:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_68);
x_487 = lean_ctor_get(x_2, 1);
lean_inc(x_487);
lean_dec(x_2);
lean_inc(x_3);
x_488 = l_Lean_Elab_Term_inferType(x_487, x_3, x_72);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
lean_inc(x_3);
x_491 = l_Lean_Elab_Term_whnf(x_489, x_3, x_490);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_491, 1);
lean_inc(x_493);
lean_dec(x_491);
x_494 = l_Lean_Expr_getAppFn___main(x_492);
x_495 = l_Lean_Elab_Term_tryPostponeIfMVar(x_492, x_3, x_493);
if (lean_obj_tag(x_495) == 0)
{
uint8_t x_496; 
x_496 = !lean_is_exclusive(x_495);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_495, 1);
x_498 = lean_ctor_get(x_495, 0);
lean_dec(x_498);
if (lean_obj_tag(x_494) == 4)
{
lean_object* x_506; 
lean_dec(x_492);
lean_dec(x_3);
x_506 = lean_ctor_get(x_494, 0);
lean_inc(x_506);
lean_dec(x_494);
lean_ctor_set(x_495, 0, x_506);
return x_495;
}
else
{
lean_object* x_507; 
lean_free_object(x_495);
lean_dec(x_494);
x_507 = lean_box(0);
x_499 = x_507;
goto block_505;
}
block_505:
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_499);
x_500 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_500, 0, x_492);
x_501 = l_Lean_indentExpr(x_500);
x_502 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_503 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_501);
x_504 = l_Lean_Elab_Term_throwError___rarg(x_503, x_3, x_497);
return x_504;
}
}
else
{
lean_object* x_508; lean_object* x_509; 
x_508 = lean_ctor_get(x_495, 1);
lean_inc(x_508);
lean_dec(x_495);
if (lean_obj_tag(x_494) == 4)
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_492);
lean_dec(x_3);
x_516 = lean_ctor_get(x_494, 0);
lean_inc(x_516);
lean_dec(x_494);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_516);
lean_ctor_set(x_517, 1, x_508);
return x_517;
}
else
{
lean_object* x_518; 
lean_dec(x_494);
x_518 = lean_box(0);
x_509 = x_518;
goto block_515;
}
block_515:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_509);
x_510 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_510, 0, x_492);
x_511 = l_Lean_indentExpr(x_510);
x_512 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_513 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_511);
x_514 = l_Lean_Elab_Term_throwError___rarg(x_513, x_3, x_508);
return x_514;
}
}
}
else
{
uint8_t x_519; 
lean_dec(x_494);
lean_dec(x_492);
lean_dec(x_3);
x_519 = !lean_is_exclusive(x_495);
if (x_519 == 0)
{
return x_495;
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_495, 0);
x_521 = lean_ctor_get(x_495, 1);
lean_inc(x_521);
lean_inc(x_520);
lean_dec(x_495);
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_520);
lean_ctor_set(x_522, 1, x_521);
return x_522;
}
}
}
else
{
uint8_t x_523; 
lean_dec(x_3);
x_523 = !lean_is_exclusive(x_491);
if (x_523 == 0)
{
return x_491;
}
else
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_524 = lean_ctor_get(x_491, 0);
x_525 = lean_ctor_get(x_491, 1);
lean_inc(x_525);
lean_inc(x_524);
lean_dec(x_491);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_524);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_3);
x_527 = !lean_is_exclusive(x_488);
if (x_527 == 0)
{
return x_488;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_488, 0);
x_529 = lean_ctor_get(x_488, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_488);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
lean_object* x_531; 
lean_dec(x_2);
x_531 = lean_box(0);
x_73 = x_531;
goto block_79;
}
}
case 11:
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_532; lean_object* x_533; 
lean_dec(x_68);
x_532 = lean_ctor_get(x_2, 1);
lean_inc(x_532);
lean_dec(x_2);
lean_inc(x_3);
x_533 = l_Lean_Elab_Term_inferType(x_532, x_3, x_72);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_3);
x_536 = l_Lean_Elab_Term_whnf(x_534, x_3, x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_536, 1);
lean_inc(x_538);
lean_dec(x_536);
x_539 = l_Lean_Expr_getAppFn___main(x_537);
x_540 = l_Lean_Elab_Term_tryPostponeIfMVar(x_537, x_3, x_538);
if (lean_obj_tag(x_540) == 0)
{
uint8_t x_541; 
x_541 = !lean_is_exclusive(x_540);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_540, 1);
x_543 = lean_ctor_get(x_540, 0);
lean_dec(x_543);
if (lean_obj_tag(x_539) == 4)
{
lean_object* x_551; 
lean_dec(x_537);
lean_dec(x_3);
x_551 = lean_ctor_get(x_539, 0);
lean_inc(x_551);
lean_dec(x_539);
lean_ctor_set(x_540, 0, x_551);
return x_540;
}
else
{
lean_object* x_552; 
lean_free_object(x_540);
lean_dec(x_539);
x_552 = lean_box(0);
x_544 = x_552;
goto block_550;
}
block_550:
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_544);
x_545 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_545, 0, x_537);
x_546 = l_Lean_indentExpr(x_545);
x_547 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_548 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_548, 0, x_547);
lean_ctor_set(x_548, 1, x_546);
x_549 = l_Lean_Elab_Term_throwError___rarg(x_548, x_3, x_542);
return x_549;
}
}
else
{
lean_object* x_553; lean_object* x_554; 
x_553 = lean_ctor_get(x_540, 1);
lean_inc(x_553);
lean_dec(x_540);
if (lean_obj_tag(x_539) == 4)
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_537);
lean_dec(x_3);
x_561 = lean_ctor_get(x_539, 0);
lean_inc(x_561);
lean_dec(x_539);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_553);
return x_562;
}
else
{
lean_object* x_563; 
lean_dec(x_539);
x_563 = lean_box(0);
x_554 = x_563;
goto block_560;
}
block_560:
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_554);
x_555 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_555, 0, x_537);
x_556 = l_Lean_indentExpr(x_555);
x_557 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_558 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = l_Lean_Elab_Term_throwError___rarg(x_558, x_3, x_553);
return x_559;
}
}
}
else
{
uint8_t x_564; 
lean_dec(x_539);
lean_dec(x_537);
lean_dec(x_3);
x_564 = !lean_is_exclusive(x_540);
if (x_564 == 0)
{
return x_540;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_540, 0);
x_566 = lean_ctor_get(x_540, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_540);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
else
{
uint8_t x_568; 
lean_dec(x_3);
x_568 = !lean_is_exclusive(x_536);
if (x_568 == 0)
{
return x_536;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_536, 0);
x_570 = lean_ctor_get(x_536, 1);
lean_inc(x_570);
lean_inc(x_569);
lean_dec(x_536);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
return x_571;
}
}
}
else
{
uint8_t x_572; 
lean_dec(x_3);
x_572 = !lean_is_exclusive(x_533);
if (x_572 == 0)
{
return x_533;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_573 = lean_ctor_get(x_533, 0);
x_574 = lean_ctor_get(x_533, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_533);
x_575 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_575, 0, x_573);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
}
else
{
lean_object* x_576; 
lean_dec(x_2);
x_576 = lean_box(0);
x_73 = x_576;
goto block_79;
}
}
default: 
{
lean_dec(x_80);
lean_free_object(x_69);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_68);
x_577 = lean_ctor_get(x_2, 1);
lean_inc(x_577);
lean_dec(x_2);
lean_inc(x_3);
x_578 = l_Lean_Elab_Term_inferType(x_577, x_3, x_72);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
lean_dec(x_578);
lean_inc(x_3);
x_581 = l_Lean_Elab_Term_whnf(x_579, x_3, x_580);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
x_584 = l_Lean_Expr_getAppFn___main(x_582);
x_585 = l_Lean_Elab_Term_tryPostponeIfMVar(x_582, x_3, x_583);
if (lean_obj_tag(x_585) == 0)
{
uint8_t x_586; 
x_586 = !lean_is_exclusive(x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_585, 1);
x_588 = lean_ctor_get(x_585, 0);
lean_dec(x_588);
if (lean_obj_tag(x_584) == 4)
{
lean_object* x_596; 
lean_dec(x_582);
lean_dec(x_3);
x_596 = lean_ctor_get(x_584, 0);
lean_inc(x_596);
lean_dec(x_584);
lean_ctor_set(x_585, 0, x_596);
return x_585;
}
else
{
lean_object* x_597; 
lean_free_object(x_585);
lean_dec(x_584);
x_597 = lean_box(0);
x_589 = x_597;
goto block_595;
}
block_595:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_589);
x_590 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_590, 0, x_582);
x_591 = l_Lean_indentExpr(x_590);
x_592 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_593 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_591);
x_594 = l_Lean_Elab_Term_throwError___rarg(x_593, x_3, x_587);
return x_594;
}
}
else
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_585, 1);
lean_inc(x_598);
lean_dec(x_585);
if (lean_obj_tag(x_584) == 4)
{
lean_object* x_606; lean_object* x_607; 
lean_dec(x_582);
lean_dec(x_3);
x_606 = lean_ctor_get(x_584, 0);
lean_inc(x_606);
lean_dec(x_584);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_598);
return x_607;
}
else
{
lean_object* x_608; 
lean_dec(x_584);
x_608 = lean_box(0);
x_599 = x_608;
goto block_605;
}
block_605:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_599);
x_600 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_600, 0, x_582);
x_601 = l_Lean_indentExpr(x_600);
x_602 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_603 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_601);
x_604 = l_Lean_Elab_Term_throwError___rarg(x_603, x_3, x_598);
return x_604;
}
}
}
else
{
uint8_t x_609; 
lean_dec(x_584);
lean_dec(x_582);
lean_dec(x_3);
x_609 = !lean_is_exclusive(x_585);
if (x_609 == 0)
{
return x_585;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_585, 0);
x_611 = lean_ctor_get(x_585, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_585);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_3);
x_613 = !lean_is_exclusive(x_581);
if (x_613 == 0)
{
return x_581;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_581, 0);
x_615 = lean_ctor_get(x_581, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_581);
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
lean_dec(x_3);
x_617 = !lean_is_exclusive(x_578);
if (x_617 == 0)
{
return x_578;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_578, 0);
x_619 = lean_ctor_get(x_578, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_578);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
else
{
lean_object* x_621; 
lean_dec(x_2);
x_621 = lean_box(0);
x_73 = x_621;
goto block_79;
}
}
}
block_79:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_68);
x_75 = l_Lean_indentExpr(x_74);
x_76 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_Lean_Elab_Term_throwError___rarg(x_77, x_3, x_72);
return x_78;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_631; 
x_622 = lean_ctor_get(x_69, 0);
x_623 = lean_ctor_get(x_69, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_69);
x_631 = l_Lean_Expr_getAppFn___main(x_622);
lean_dec(x_622);
switch (lean_obj_tag(x_631)) {
case 0:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_68);
x_632 = lean_ctor_get(x_2, 1);
lean_inc(x_632);
lean_dec(x_2);
lean_inc(x_3);
x_633 = l_Lean_Elab_Term_inferType(x_632, x_3, x_623);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_633, 1);
lean_inc(x_635);
lean_dec(x_633);
lean_inc(x_3);
x_636 = l_Lean_Elab_Term_whnf(x_634, x_3, x_635);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_636, 1);
lean_inc(x_638);
lean_dec(x_636);
x_639 = l_Lean_Expr_getAppFn___main(x_637);
x_640 = l_Lean_Elab_Term_tryPostponeIfMVar(x_637, x_3, x_638);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_640, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_642 = x_640;
} else {
 lean_dec_ref(x_640);
 x_642 = lean_box(0);
}
if (lean_obj_tag(x_639) == 4)
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_637);
lean_dec(x_3);
x_650 = lean_ctor_get(x_639, 0);
lean_inc(x_650);
lean_dec(x_639);
if (lean_is_scalar(x_642)) {
 x_651 = lean_alloc_ctor(0, 2, 0);
} else {
 x_651 = x_642;
}
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_641);
return x_651;
}
else
{
lean_object* x_652; 
lean_dec(x_642);
lean_dec(x_639);
x_652 = lean_box(0);
x_643 = x_652;
goto block_649;
}
block_649:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_643);
x_644 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_644, 0, x_637);
x_645 = l_Lean_indentExpr(x_644);
x_646 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_647 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_645);
x_648 = l_Lean_Elab_Term_throwError___rarg(x_647, x_3, x_641);
return x_648;
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_639);
lean_dec(x_637);
lean_dec(x_3);
x_653 = lean_ctor_get(x_640, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_640, 1);
lean_inc(x_654);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 lean_ctor_release(x_640, 1);
 x_655 = x_640;
} else {
 lean_dec_ref(x_640);
 x_655 = lean_box(0);
}
if (lean_is_scalar(x_655)) {
 x_656 = lean_alloc_ctor(1, 2, 0);
} else {
 x_656 = x_655;
}
lean_ctor_set(x_656, 0, x_653);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_3);
x_657 = lean_ctor_get(x_636, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_636, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_659 = x_636;
} else {
 lean_dec_ref(x_636);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 2, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_657);
lean_ctor_set(x_660, 1, x_658);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_3);
x_661 = lean_ctor_get(x_633, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_633, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_663 = x_633;
} else {
 lean_dec_ref(x_633);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
return x_664;
}
}
else
{
lean_object* x_665; 
lean_dec(x_2);
x_665 = lean_box(0);
x_624 = x_665;
goto block_630;
}
}
case 1:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_666; lean_object* x_667; 
lean_dec(x_68);
x_666 = lean_ctor_get(x_2, 1);
lean_inc(x_666);
lean_dec(x_2);
lean_inc(x_3);
x_667 = l_Lean_Elab_Term_inferType(x_666, x_3, x_623);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
x_669 = lean_ctor_get(x_667, 1);
lean_inc(x_669);
lean_dec(x_667);
lean_inc(x_3);
x_670 = l_Lean_Elab_Term_whnf(x_668, x_3, x_669);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
x_673 = l_Lean_Expr_getAppFn___main(x_671);
x_674 = l_Lean_Elab_Term_tryPostponeIfMVar(x_671, x_3, x_672);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_676 = x_674;
} else {
 lean_dec_ref(x_674);
 x_676 = lean_box(0);
}
if (lean_obj_tag(x_673) == 4)
{
lean_object* x_684; lean_object* x_685; 
lean_dec(x_671);
lean_dec(x_3);
x_684 = lean_ctor_get(x_673, 0);
lean_inc(x_684);
lean_dec(x_673);
if (lean_is_scalar(x_676)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_676;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_675);
return x_685;
}
else
{
lean_object* x_686; 
lean_dec(x_676);
lean_dec(x_673);
x_686 = lean_box(0);
x_677 = x_686;
goto block_683;
}
block_683:
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_677);
x_678 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_678, 0, x_671);
x_679 = l_Lean_indentExpr(x_678);
x_680 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_681 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_679);
x_682 = l_Lean_Elab_Term_throwError___rarg(x_681, x_3, x_675);
return x_682;
}
}
else
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
lean_dec(x_673);
lean_dec(x_671);
lean_dec(x_3);
x_687 = lean_ctor_get(x_674, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_674, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_689 = x_674;
} else {
 lean_dec_ref(x_674);
 x_689 = lean_box(0);
}
if (lean_is_scalar(x_689)) {
 x_690 = lean_alloc_ctor(1, 2, 0);
} else {
 x_690 = x_689;
}
lean_ctor_set(x_690, 0, x_687);
lean_ctor_set(x_690, 1, x_688);
return x_690;
}
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_3);
x_691 = lean_ctor_get(x_670, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_670, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_693 = x_670;
} else {
 lean_dec_ref(x_670);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_3);
x_695 = lean_ctor_get(x_667, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_667, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_697 = x_667;
} else {
 lean_dec_ref(x_667);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
lean_object* x_699; 
lean_dec(x_2);
x_699 = lean_box(0);
x_624 = x_699;
goto block_630;
}
}
case 2:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_700; lean_object* x_701; 
lean_dec(x_68);
x_700 = lean_ctor_get(x_2, 1);
lean_inc(x_700);
lean_dec(x_2);
lean_inc(x_3);
x_701 = l_Lean_Elab_Term_inferType(x_700, x_3, x_623);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_701, 1);
lean_inc(x_703);
lean_dec(x_701);
lean_inc(x_3);
x_704 = l_Lean_Elab_Term_whnf(x_702, x_3, x_703);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_704, 1);
lean_inc(x_706);
lean_dec(x_704);
x_707 = l_Lean_Expr_getAppFn___main(x_705);
x_708 = l_Lean_Elab_Term_tryPostponeIfMVar(x_705, x_3, x_706);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_708, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_710 = x_708;
} else {
 lean_dec_ref(x_708);
 x_710 = lean_box(0);
}
if (lean_obj_tag(x_707) == 4)
{
lean_object* x_718; lean_object* x_719; 
lean_dec(x_705);
lean_dec(x_3);
x_718 = lean_ctor_get(x_707, 0);
lean_inc(x_718);
lean_dec(x_707);
if (lean_is_scalar(x_710)) {
 x_719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_719 = x_710;
}
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_709);
return x_719;
}
else
{
lean_object* x_720; 
lean_dec(x_710);
lean_dec(x_707);
x_720 = lean_box(0);
x_711 = x_720;
goto block_717;
}
block_717:
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_711);
x_712 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_712, 0, x_705);
x_713 = l_Lean_indentExpr(x_712);
x_714 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_715 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_715, 1, x_713);
x_716 = l_Lean_Elab_Term_throwError___rarg(x_715, x_3, x_709);
return x_716;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
lean_dec(x_707);
lean_dec(x_705);
lean_dec(x_3);
x_721 = lean_ctor_get(x_708, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_708, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_723 = x_708;
} else {
 lean_dec_ref(x_708);
 x_723 = lean_box(0);
}
if (lean_is_scalar(x_723)) {
 x_724 = lean_alloc_ctor(1, 2, 0);
} else {
 x_724 = x_723;
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_722);
return x_724;
}
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_3);
x_725 = lean_ctor_get(x_704, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_704, 1);
lean_inc(x_726);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_727 = x_704;
} else {
 lean_dec_ref(x_704);
 x_727 = lean_box(0);
}
if (lean_is_scalar(x_727)) {
 x_728 = lean_alloc_ctor(1, 2, 0);
} else {
 x_728 = x_727;
}
lean_ctor_set(x_728, 0, x_725);
lean_ctor_set(x_728, 1, x_726);
return x_728;
}
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_3);
x_729 = lean_ctor_get(x_701, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_701, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_731 = x_701;
} else {
 lean_dec_ref(x_701);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
else
{
lean_object* x_733; 
lean_dec(x_2);
x_733 = lean_box(0);
x_624 = x_733;
goto block_630;
}
}
case 3:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_734; lean_object* x_735; 
lean_dec(x_68);
x_734 = lean_ctor_get(x_2, 1);
lean_inc(x_734);
lean_dec(x_2);
lean_inc(x_3);
x_735 = l_Lean_Elab_Term_inferType(x_734, x_3, x_623);
if (lean_obj_tag(x_735) == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_735, 1);
lean_inc(x_737);
lean_dec(x_735);
lean_inc(x_3);
x_738 = l_Lean_Elab_Term_whnf(x_736, x_3, x_737);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_739 = lean_ctor_get(x_738, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_738, 1);
lean_inc(x_740);
lean_dec(x_738);
x_741 = l_Lean_Expr_getAppFn___main(x_739);
x_742 = l_Lean_Elab_Term_tryPostponeIfMVar(x_739, x_3, x_740);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_744 = x_742;
} else {
 lean_dec_ref(x_742);
 x_744 = lean_box(0);
}
if (lean_obj_tag(x_741) == 4)
{
lean_object* x_752; lean_object* x_753; 
lean_dec(x_739);
lean_dec(x_3);
x_752 = lean_ctor_get(x_741, 0);
lean_inc(x_752);
lean_dec(x_741);
if (lean_is_scalar(x_744)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_744;
}
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_743);
return x_753;
}
else
{
lean_object* x_754; 
lean_dec(x_744);
lean_dec(x_741);
x_754 = lean_box(0);
x_745 = x_754;
goto block_751;
}
block_751:
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_745);
x_746 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_746, 0, x_739);
x_747 = l_Lean_indentExpr(x_746);
x_748 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_749 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_747);
x_750 = l_Lean_Elab_Term_throwError___rarg(x_749, x_3, x_743);
return x_750;
}
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_741);
lean_dec(x_739);
lean_dec(x_3);
x_755 = lean_ctor_get(x_742, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_742, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_757 = x_742;
} else {
 lean_dec_ref(x_742);
 x_757 = lean_box(0);
}
if (lean_is_scalar(x_757)) {
 x_758 = lean_alloc_ctor(1, 2, 0);
} else {
 x_758 = x_757;
}
lean_ctor_set(x_758, 0, x_755);
lean_ctor_set(x_758, 1, x_756);
return x_758;
}
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_3);
x_759 = lean_ctor_get(x_738, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_738, 1);
lean_inc(x_760);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 lean_ctor_release(x_738, 1);
 x_761 = x_738;
} else {
 lean_dec_ref(x_738);
 x_761 = lean_box(0);
}
if (lean_is_scalar(x_761)) {
 x_762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_762 = x_761;
}
lean_ctor_set(x_762, 0, x_759);
lean_ctor_set(x_762, 1, x_760);
return x_762;
}
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_3);
x_763 = lean_ctor_get(x_735, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_735, 1);
lean_inc(x_764);
if (lean_is_exclusive(x_735)) {
 lean_ctor_release(x_735, 0);
 lean_ctor_release(x_735, 1);
 x_765 = x_735;
} else {
 lean_dec_ref(x_735);
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
else
{
lean_object* x_767; 
lean_dec(x_2);
x_767 = lean_box(0);
x_624 = x_767;
goto block_630;
}
}
case 4:
{
lean_object* x_768; lean_object* x_769; 
lean_dec(x_68);
lean_dec(x_3);
lean_dec(x_2);
x_768 = lean_ctor_get(x_631, 0);
lean_inc(x_768);
lean_dec(x_631);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_623);
return x_769;
}
case 5:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_770; lean_object* x_771; 
lean_dec(x_68);
x_770 = lean_ctor_get(x_2, 1);
lean_inc(x_770);
lean_dec(x_2);
lean_inc(x_3);
x_771 = l_Lean_Elab_Term_inferType(x_770, x_3, x_623);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
lean_inc(x_3);
x_774 = l_Lean_Elab_Term_whnf(x_772, x_3, x_773);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
lean_dec(x_774);
x_777 = l_Lean_Expr_getAppFn___main(x_775);
x_778 = l_Lean_Elab_Term_tryPostponeIfMVar(x_775, x_3, x_776);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_780 = x_778;
} else {
 lean_dec_ref(x_778);
 x_780 = lean_box(0);
}
if (lean_obj_tag(x_777) == 4)
{
lean_object* x_788; lean_object* x_789; 
lean_dec(x_775);
lean_dec(x_3);
x_788 = lean_ctor_get(x_777, 0);
lean_inc(x_788);
lean_dec(x_777);
if (lean_is_scalar(x_780)) {
 x_789 = lean_alloc_ctor(0, 2, 0);
} else {
 x_789 = x_780;
}
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_779);
return x_789;
}
else
{
lean_object* x_790; 
lean_dec(x_780);
lean_dec(x_777);
x_790 = lean_box(0);
x_781 = x_790;
goto block_787;
}
block_787:
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
lean_dec(x_781);
x_782 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_782, 0, x_775);
x_783 = l_Lean_indentExpr(x_782);
x_784 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_785 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_783);
x_786 = l_Lean_Elab_Term_throwError___rarg(x_785, x_3, x_779);
return x_786;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_777);
lean_dec(x_775);
lean_dec(x_3);
x_791 = lean_ctor_get(x_778, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_778, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_793 = x_778;
} else {
 lean_dec_ref(x_778);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
return x_794;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_3);
x_795 = lean_ctor_get(x_774, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_774, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_797 = x_774;
} else {
 lean_dec_ref(x_774);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
return x_798;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_3);
x_799 = lean_ctor_get(x_771, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_771, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_801 = x_771;
} else {
 lean_dec_ref(x_771);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_800);
return x_802;
}
}
else
{
lean_object* x_803; 
lean_dec(x_2);
x_803 = lean_box(0);
x_624 = x_803;
goto block_630;
}
}
case 6:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_804; lean_object* x_805; 
lean_dec(x_68);
x_804 = lean_ctor_get(x_2, 1);
lean_inc(x_804);
lean_dec(x_2);
lean_inc(x_3);
x_805 = l_Lean_Elab_Term_inferType(x_804, x_3, x_623);
if (lean_obj_tag(x_805) == 0)
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_ctor_get(x_805, 1);
lean_inc(x_807);
lean_dec(x_805);
lean_inc(x_3);
x_808 = l_Lean_Elab_Term_whnf(x_806, x_3, x_807);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
lean_dec(x_808);
x_811 = l_Lean_Expr_getAppFn___main(x_809);
x_812 = l_Lean_Elab_Term_tryPostponeIfMVar(x_809, x_3, x_810);
if (lean_obj_tag(x_812) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_813 = lean_ctor_get(x_812, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_814 = x_812;
} else {
 lean_dec_ref(x_812);
 x_814 = lean_box(0);
}
if (lean_obj_tag(x_811) == 4)
{
lean_object* x_822; lean_object* x_823; 
lean_dec(x_809);
lean_dec(x_3);
x_822 = lean_ctor_get(x_811, 0);
lean_inc(x_822);
lean_dec(x_811);
if (lean_is_scalar(x_814)) {
 x_823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_823 = x_814;
}
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_813);
return x_823;
}
else
{
lean_object* x_824; 
lean_dec(x_814);
lean_dec(x_811);
x_824 = lean_box(0);
x_815 = x_824;
goto block_821;
}
block_821:
{
lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
lean_dec(x_815);
x_816 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_816, 0, x_809);
x_817 = l_Lean_indentExpr(x_816);
x_818 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_819 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_817);
x_820 = l_Lean_Elab_Term_throwError___rarg(x_819, x_3, x_813);
return x_820;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_811);
lean_dec(x_809);
lean_dec(x_3);
x_825 = lean_ctor_get(x_812, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_812, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_812)) {
 lean_ctor_release(x_812, 0);
 lean_ctor_release(x_812, 1);
 x_827 = x_812;
} else {
 lean_dec_ref(x_812);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_825);
lean_ctor_set(x_828, 1, x_826);
return x_828;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_3);
x_829 = lean_ctor_get(x_808, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_808, 1);
lean_inc(x_830);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_831 = x_808;
} else {
 lean_dec_ref(x_808);
 x_831 = lean_box(0);
}
if (lean_is_scalar(x_831)) {
 x_832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_832 = x_831;
}
lean_ctor_set(x_832, 0, x_829);
lean_ctor_set(x_832, 1, x_830);
return x_832;
}
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_3);
x_833 = lean_ctor_get(x_805, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_805, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_805)) {
 lean_ctor_release(x_805, 0);
 lean_ctor_release(x_805, 1);
 x_835 = x_805;
} else {
 lean_dec_ref(x_805);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
else
{
lean_object* x_837; 
lean_dec(x_2);
x_837 = lean_box(0);
x_624 = x_837;
goto block_630;
}
}
case 7:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_838; lean_object* x_839; 
lean_dec(x_68);
x_838 = lean_ctor_get(x_2, 1);
lean_inc(x_838);
lean_dec(x_2);
lean_inc(x_3);
x_839 = l_Lean_Elab_Term_inferType(x_838, x_3, x_623);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_840 = lean_ctor_get(x_839, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_839, 1);
lean_inc(x_841);
lean_dec(x_839);
lean_inc(x_3);
x_842 = l_Lean_Elab_Term_whnf(x_840, x_3, x_841);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
x_843 = lean_ctor_get(x_842, 0);
lean_inc(x_843);
x_844 = lean_ctor_get(x_842, 1);
lean_inc(x_844);
lean_dec(x_842);
x_845 = l_Lean_Expr_getAppFn___main(x_843);
x_846 = l_Lean_Elab_Term_tryPostponeIfMVar(x_843, x_3, x_844);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 x_848 = x_846;
} else {
 lean_dec_ref(x_846);
 x_848 = lean_box(0);
}
if (lean_obj_tag(x_845) == 4)
{
lean_object* x_856; lean_object* x_857; 
lean_dec(x_843);
lean_dec(x_3);
x_856 = lean_ctor_get(x_845, 0);
lean_inc(x_856);
lean_dec(x_845);
if (lean_is_scalar(x_848)) {
 x_857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_857 = x_848;
}
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_847);
return x_857;
}
else
{
lean_object* x_858; 
lean_dec(x_848);
lean_dec(x_845);
x_858 = lean_box(0);
x_849 = x_858;
goto block_855;
}
block_855:
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_849);
x_850 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_850, 0, x_843);
x_851 = l_Lean_indentExpr(x_850);
x_852 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_853 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_851);
x_854 = l_Lean_Elab_Term_throwError___rarg(x_853, x_3, x_847);
return x_854;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_845);
lean_dec(x_843);
lean_dec(x_3);
x_859 = lean_ctor_get(x_846, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_846, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_846)) {
 lean_ctor_release(x_846, 0);
 lean_ctor_release(x_846, 1);
 x_861 = x_846;
} else {
 lean_dec_ref(x_846);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_3);
x_863 = lean_ctor_get(x_842, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_842, 1);
lean_inc(x_864);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_865 = x_842;
} else {
 lean_dec_ref(x_842);
 x_865 = lean_box(0);
}
if (lean_is_scalar(x_865)) {
 x_866 = lean_alloc_ctor(1, 2, 0);
} else {
 x_866 = x_865;
}
lean_ctor_set(x_866, 0, x_863);
lean_ctor_set(x_866, 1, x_864);
return x_866;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; 
lean_dec(x_3);
x_867 = lean_ctor_get(x_839, 0);
lean_inc(x_867);
x_868 = lean_ctor_get(x_839, 1);
lean_inc(x_868);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_869 = x_839;
} else {
 lean_dec_ref(x_839);
 x_869 = lean_box(0);
}
if (lean_is_scalar(x_869)) {
 x_870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_870 = x_869;
}
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_868);
return x_870;
}
}
else
{
lean_object* x_871; 
lean_dec(x_2);
x_871 = lean_box(0);
x_624 = x_871;
goto block_630;
}
}
case 8:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_872; lean_object* x_873; 
lean_dec(x_68);
x_872 = lean_ctor_get(x_2, 1);
lean_inc(x_872);
lean_dec(x_2);
lean_inc(x_3);
x_873 = l_Lean_Elab_Term_inferType(x_872, x_3, x_623);
if (lean_obj_tag(x_873) == 0)
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_ctor_get(x_873, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_873, 1);
lean_inc(x_875);
lean_dec(x_873);
lean_inc(x_3);
x_876 = l_Lean_Elab_Term_whnf(x_874, x_3, x_875);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_877 = lean_ctor_get(x_876, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_876, 1);
lean_inc(x_878);
lean_dec(x_876);
x_879 = l_Lean_Expr_getAppFn___main(x_877);
x_880 = l_Lean_Elab_Term_tryPostponeIfMVar(x_877, x_3, x_878);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_880, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_882 = x_880;
} else {
 lean_dec_ref(x_880);
 x_882 = lean_box(0);
}
if (lean_obj_tag(x_879) == 4)
{
lean_object* x_890; lean_object* x_891; 
lean_dec(x_877);
lean_dec(x_3);
x_890 = lean_ctor_get(x_879, 0);
lean_inc(x_890);
lean_dec(x_879);
if (lean_is_scalar(x_882)) {
 x_891 = lean_alloc_ctor(0, 2, 0);
} else {
 x_891 = x_882;
}
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_881);
return x_891;
}
else
{
lean_object* x_892; 
lean_dec(x_882);
lean_dec(x_879);
x_892 = lean_box(0);
x_883 = x_892;
goto block_889;
}
block_889:
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_883);
x_884 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_884, 0, x_877);
x_885 = l_Lean_indentExpr(x_884);
x_886 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_887 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_887, 0, x_886);
lean_ctor_set(x_887, 1, x_885);
x_888 = l_Lean_Elab_Term_throwError___rarg(x_887, x_3, x_881);
return x_888;
}
}
else
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; 
lean_dec(x_879);
lean_dec(x_877);
lean_dec(x_3);
x_893 = lean_ctor_get(x_880, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_880, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_895 = x_880;
} else {
 lean_dec_ref(x_880);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_895)) {
 x_896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_896 = x_895;
}
lean_ctor_set(x_896, 0, x_893);
lean_ctor_set(x_896, 1, x_894);
return x_896;
}
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_3);
x_897 = lean_ctor_get(x_876, 0);
lean_inc(x_897);
x_898 = lean_ctor_get(x_876, 1);
lean_inc(x_898);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_899 = x_876;
} else {
 lean_dec_ref(x_876);
 x_899 = lean_box(0);
}
if (lean_is_scalar(x_899)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_899;
}
lean_ctor_set(x_900, 0, x_897);
lean_ctor_set(x_900, 1, x_898);
return x_900;
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_3);
x_901 = lean_ctor_get(x_873, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_873, 1);
lean_inc(x_902);
if (lean_is_exclusive(x_873)) {
 lean_ctor_release(x_873, 0);
 lean_ctor_release(x_873, 1);
 x_903 = x_873;
} else {
 lean_dec_ref(x_873);
 x_903 = lean_box(0);
}
if (lean_is_scalar(x_903)) {
 x_904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_904 = x_903;
}
lean_ctor_set(x_904, 0, x_901);
lean_ctor_set(x_904, 1, x_902);
return x_904;
}
}
else
{
lean_object* x_905; 
lean_dec(x_2);
x_905 = lean_box(0);
x_624 = x_905;
goto block_630;
}
}
case 9:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_68);
x_906 = lean_ctor_get(x_2, 1);
lean_inc(x_906);
lean_dec(x_2);
lean_inc(x_3);
x_907 = l_Lean_Elab_Term_inferType(x_906, x_3, x_623);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
lean_dec(x_907);
lean_inc(x_3);
x_910 = l_Lean_Elab_Term_whnf(x_908, x_3, x_909);
if (lean_obj_tag(x_910) == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_911 = lean_ctor_get(x_910, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_910, 1);
lean_inc(x_912);
lean_dec(x_910);
x_913 = l_Lean_Expr_getAppFn___main(x_911);
x_914 = l_Lean_Elab_Term_tryPostponeIfMVar(x_911, x_3, x_912);
if (lean_obj_tag(x_914) == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; 
x_915 = lean_ctor_get(x_914, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_916 = x_914;
} else {
 lean_dec_ref(x_914);
 x_916 = lean_box(0);
}
if (lean_obj_tag(x_913) == 4)
{
lean_object* x_924; lean_object* x_925; 
lean_dec(x_911);
lean_dec(x_3);
x_924 = lean_ctor_get(x_913, 0);
lean_inc(x_924);
lean_dec(x_913);
if (lean_is_scalar(x_916)) {
 x_925 = lean_alloc_ctor(0, 2, 0);
} else {
 x_925 = x_916;
}
lean_ctor_set(x_925, 0, x_924);
lean_ctor_set(x_925, 1, x_915);
return x_925;
}
else
{
lean_object* x_926; 
lean_dec(x_916);
lean_dec(x_913);
x_926 = lean_box(0);
x_917 = x_926;
goto block_923;
}
block_923:
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_917);
x_918 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_918, 0, x_911);
x_919 = l_Lean_indentExpr(x_918);
x_920 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_921 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_919);
x_922 = l_Lean_Elab_Term_throwError___rarg(x_921, x_3, x_915);
return x_922;
}
}
else
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_913);
lean_dec(x_911);
lean_dec(x_3);
x_927 = lean_ctor_get(x_914, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_914, 1);
lean_inc(x_928);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_929 = x_914;
} else {
 lean_dec_ref(x_914);
 x_929 = lean_box(0);
}
if (lean_is_scalar(x_929)) {
 x_930 = lean_alloc_ctor(1, 2, 0);
} else {
 x_930 = x_929;
}
lean_ctor_set(x_930, 0, x_927);
lean_ctor_set(x_930, 1, x_928);
return x_930;
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_3);
x_931 = lean_ctor_get(x_910, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_910, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_910)) {
 lean_ctor_release(x_910, 0);
 lean_ctor_release(x_910, 1);
 x_933 = x_910;
} else {
 lean_dec_ref(x_910);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_932);
return x_934;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_3);
x_935 = lean_ctor_get(x_907, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_907, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_937 = x_907;
} else {
 lean_dec_ref(x_907);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
return x_938;
}
}
else
{
lean_object* x_939; 
lean_dec(x_2);
x_939 = lean_box(0);
x_624 = x_939;
goto block_630;
}
}
case 10:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_940; lean_object* x_941; 
lean_dec(x_68);
x_940 = lean_ctor_get(x_2, 1);
lean_inc(x_940);
lean_dec(x_2);
lean_inc(x_3);
x_941 = l_Lean_Elab_Term_inferType(x_940, x_3, x_623);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_ctor_get(x_941, 1);
lean_inc(x_943);
lean_dec(x_941);
lean_inc(x_3);
x_944 = l_Lean_Elab_Term_whnf(x_942, x_3, x_943);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
x_947 = l_Lean_Expr_getAppFn___main(x_945);
x_948 = l_Lean_Elab_Term_tryPostponeIfMVar(x_945, x_3, x_946);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = lean_ctor_get(x_948, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_950 = x_948;
} else {
 lean_dec_ref(x_948);
 x_950 = lean_box(0);
}
if (lean_obj_tag(x_947) == 4)
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_945);
lean_dec(x_3);
x_958 = lean_ctor_get(x_947, 0);
lean_inc(x_958);
lean_dec(x_947);
if (lean_is_scalar(x_950)) {
 x_959 = lean_alloc_ctor(0, 2, 0);
} else {
 x_959 = x_950;
}
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_949);
return x_959;
}
else
{
lean_object* x_960; 
lean_dec(x_950);
lean_dec(x_947);
x_960 = lean_box(0);
x_951 = x_960;
goto block_957;
}
block_957:
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_951);
x_952 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_952, 0, x_945);
x_953 = l_Lean_indentExpr(x_952);
x_954 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_955 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_953);
x_956 = l_Lean_Elab_Term_throwError___rarg(x_955, x_3, x_949);
return x_956;
}
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
lean_dec(x_947);
lean_dec(x_945);
lean_dec(x_3);
x_961 = lean_ctor_get(x_948, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_948, 1);
lean_inc(x_962);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_963 = x_948;
} else {
 lean_dec_ref(x_948);
 x_963 = lean_box(0);
}
if (lean_is_scalar(x_963)) {
 x_964 = lean_alloc_ctor(1, 2, 0);
} else {
 x_964 = x_963;
}
lean_ctor_set(x_964, 0, x_961);
lean_ctor_set(x_964, 1, x_962);
return x_964;
}
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_3);
x_965 = lean_ctor_get(x_944, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_944, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_944)) {
 lean_ctor_release(x_944, 0);
 lean_ctor_release(x_944, 1);
 x_967 = x_944;
} else {
 lean_dec_ref(x_944);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(1, 2, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_965);
lean_ctor_set(x_968, 1, x_966);
return x_968;
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
lean_dec(x_3);
x_969 = lean_ctor_get(x_941, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_941, 1);
lean_inc(x_970);
if (lean_is_exclusive(x_941)) {
 lean_ctor_release(x_941, 0);
 lean_ctor_release(x_941, 1);
 x_971 = x_941;
} else {
 lean_dec_ref(x_941);
 x_971 = lean_box(0);
}
if (lean_is_scalar(x_971)) {
 x_972 = lean_alloc_ctor(1, 2, 0);
} else {
 x_972 = x_971;
}
lean_ctor_set(x_972, 0, x_969);
lean_ctor_set(x_972, 1, x_970);
return x_972;
}
}
else
{
lean_object* x_973; 
lean_dec(x_2);
x_973 = lean_box(0);
x_624 = x_973;
goto block_630;
}
}
case 11:
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_974; lean_object* x_975; 
lean_dec(x_68);
x_974 = lean_ctor_get(x_2, 1);
lean_inc(x_974);
lean_dec(x_2);
lean_inc(x_3);
x_975 = l_Lean_Elab_Term_inferType(x_974, x_3, x_623);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_976 = lean_ctor_get(x_975, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_975, 1);
lean_inc(x_977);
lean_dec(x_975);
lean_inc(x_3);
x_978 = l_Lean_Elab_Term_whnf(x_976, x_3, x_977);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_979 = lean_ctor_get(x_978, 0);
lean_inc(x_979);
x_980 = lean_ctor_get(x_978, 1);
lean_inc(x_980);
lean_dec(x_978);
x_981 = l_Lean_Expr_getAppFn___main(x_979);
x_982 = l_Lean_Elab_Term_tryPostponeIfMVar(x_979, x_3, x_980);
if (lean_obj_tag(x_982) == 0)
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_983 = lean_ctor_get(x_982, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_984 = x_982;
} else {
 lean_dec_ref(x_982);
 x_984 = lean_box(0);
}
if (lean_obj_tag(x_981) == 4)
{
lean_object* x_992; lean_object* x_993; 
lean_dec(x_979);
lean_dec(x_3);
x_992 = lean_ctor_get(x_981, 0);
lean_inc(x_992);
lean_dec(x_981);
if (lean_is_scalar(x_984)) {
 x_993 = lean_alloc_ctor(0, 2, 0);
} else {
 x_993 = x_984;
}
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_983);
return x_993;
}
else
{
lean_object* x_994; 
lean_dec(x_984);
lean_dec(x_981);
x_994 = lean_box(0);
x_985 = x_994;
goto block_991;
}
block_991:
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_dec(x_985);
x_986 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_986, 0, x_979);
x_987 = l_Lean_indentExpr(x_986);
x_988 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_989 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_989, 0, x_988);
lean_ctor_set(x_989, 1, x_987);
x_990 = l_Lean_Elab_Term_throwError___rarg(x_989, x_3, x_983);
return x_990;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_3);
x_995 = lean_ctor_get(x_982, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_982, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_997 = x_982;
} else {
 lean_dec_ref(x_982);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_3);
x_999 = lean_ctor_get(x_978, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_978, 1);
lean_inc(x_1000);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_1001 = x_978;
} else {
 lean_dec_ref(x_978);
 x_1001 = lean_box(0);
}
if (lean_is_scalar(x_1001)) {
 x_1002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1002 = x_1001;
}
lean_ctor_set(x_1002, 0, x_999);
lean_ctor_set(x_1002, 1, x_1000);
return x_1002;
}
}
else
{
lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_3);
x_1003 = lean_ctor_get(x_975, 0);
lean_inc(x_1003);
x_1004 = lean_ctor_get(x_975, 1);
lean_inc(x_1004);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_1005 = x_975;
} else {
 lean_dec_ref(x_975);
 x_1005 = lean_box(0);
}
if (lean_is_scalar(x_1005)) {
 x_1006 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1006 = x_1005;
}
lean_ctor_set(x_1006, 0, x_1003);
lean_ctor_set(x_1006, 1, x_1004);
return x_1006;
}
}
else
{
lean_object* x_1007; 
lean_dec(x_2);
x_1007 = lean_box(0);
x_624 = x_1007;
goto block_630;
}
}
default: 
{
lean_dec(x_631);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_1008; lean_object* x_1009; 
lean_dec(x_68);
x_1008 = lean_ctor_get(x_2, 1);
lean_inc(x_1008);
lean_dec(x_2);
lean_inc(x_3);
x_1009 = l_Lean_Elab_Term_inferType(x_1008, x_3, x_623);
if (lean_obj_tag(x_1009) == 0)
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_1009, 0);
lean_inc(x_1010);
x_1011 = lean_ctor_get(x_1009, 1);
lean_inc(x_1011);
lean_dec(x_1009);
lean_inc(x_3);
x_1012 = l_Lean_Elab_Term_whnf(x_1010, x_3, x_1011);
if (lean_obj_tag(x_1012) == 0)
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1013 = lean_ctor_get(x_1012, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_1012, 1);
lean_inc(x_1014);
lean_dec(x_1012);
x_1015 = l_Lean_Expr_getAppFn___main(x_1013);
x_1016 = l_Lean_Elab_Term_tryPostponeIfMVar(x_1013, x_3, x_1014);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_1016, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1018 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1018 = lean_box(0);
}
if (lean_obj_tag(x_1015) == 4)
{
lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_1013);
lean_dec(x_3);
x_1026 = lean_ctor_get(x_1015, 0);
lean_inc(x_1026);
lean_dec(x_1015);
if (lean_is_scalar(x_1018)) {
 x_1027 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1027 = x_1018;
}
lean_ctor_set(x_1027, 0, x_1026);
lean_ctor_set(x_1027, 1, x_1017);
return x_1027;
}
else
{
lean_object* x_1028; 
lean_dec(x_1018);
lean_dec(x_1015);
x_1028 = lean_box(0);
x_1019 = x_1028;
goto block_1025;
}
block_1025:
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
lean_dec(x_1019);
x_1020 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1020, 0, x_1013);
x_1021 = l_Lean_indentExpr(x_1020);
x_1022 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_1023 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1021);
x_1024 = l_Lean_Elab_Term_throwError___rarg(x_1023, x_3, x_1017);
return x_1024;
}
}
else
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_1015);
lean_dec(x_1013);
lean_dec(x_3);
x_1029 = lean_ctor_get(x_1016, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1016, 1);
lean_inc(x_1030);
if (lean_is_exclusive(x_1016)) {
 lean_ctor_release(x_1016, 0);
 lean_ctor_release(x_1016, 1);
 x_1031 = x_1016;
} else {
 lean_dec_ref(x_1016);
 x_1031 = lean_box(0);
}
if (lean_is_scalar(x_1031)) {
 x_1032 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1032 = x_1031;
}
lean_ctor_set(x_1032, 0, x_1029);
lean_ctor_set(x_1032, 1, x_1030);
return x_1032;
}
}
else
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_3);
x_1033 = lean_ctor_get(x_1012, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1012, 1);
lean_inc(x_1034);
if (lean_is_exclusive(x_1012)) {
 lean_ctor_release(x_1012, 0);
 lean_ctor_release(x_1012, 1);
 x_1035 = x_1012;
} else {
 lean_dec_ref(x_1012);
 x_1035 = lean_box(0);
}
if (lean_is_scalar(x_1035)) {
 x_1036 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1036 = x_1035;
}
lean_ctor_set(x_1036, 0, x_1033);
lean_ctor_set(x_1036, 1, x_1034);
return x_1036;
}
}
else
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
lean_dec(x_3);
x_1037 = lean_ctor_get(x_1009, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1009, 1);
lean_inc(x_1038);
if (lean_is_exclusive(x_1009)) {
 lean_ctor_release(x_1009, 0);
 lean_ctor_release(x_1009, 1);
 x_1039 = x_1009;
} else {
 lean_dec_ref(x_1009);
 x_1039 = lean_box(0);
}
if (lean_is_scalar(x_1039)) {
 x_1040 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1040 = x_1039;
}
lean_ctor_set(x_1040, 0, x_1037);
lean_ctor_set(x_1040, 1, x_1038);
return x_1040;
}
}
else
{
lean_object* x_1041; 
lean_dec(x_2);
x_1041 = lean_box(0);
x_624 = x_1041;
goto block_630;
}
}
}
block_630:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_624);
x_625 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_625, 0, x_68);
x_626 = l_Lean_indentExpr(x_625);
x_627 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_628 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_626);
x_629 = l_Lean_Elab_Term_throwError___rarg(x_628, x_3, x_623);
return x_629;
}
}
}
else
{
uint8_t x_1042; 
lean_dec(x_68);
lean_dec(x_3);
lean_dec(x_2);
x_1042 = !lean_is_exclusive(x_69);
if (x_1042 == 0)
{
return x_69;
}
else
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
x_1043 = lean_ctor_get(x_69, 0);
x_1044 = lean_ctor_get(x_69, 1);
lean_inc(x_1044);
lean_inc(x_1043);
lean_dec(x_69);
x_1045 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1045, 0, x_1043);
lean_ctor_set(x_1045, 1, x_1044);
return x_1045;
}
}
}
block_22:
{
lean_dec(x_7);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Expr_Inhabited;
x_9 = l_Option_get_x21___rarg___closed__3;
x_10 = lean_panic_fn(x_8, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_indentExpr(x_11);
x_13 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_Term_throwError___rarg(x_14, x_3, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_indentExpr(x_17);
x_19 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_Elab_Term_throwError___rarg(x_20, x_3, x_6);
return x_21;
}
}
}
else
{
uint8_t x_1046; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1046 = !lean_is_exclusive(x_5);
if (x_1046 == 0)
{
return x_5;
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
x_1047 = lean_ctor_get(x_5, 0);
x_1048 = lean_ctor_get(x_5, 1);
lean_inc(x_1048);
lean_inc(x_1047);
lean_dec(x_5);
x_1049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1049, 0, x_1047);
lean_ctor_set(x_1049, 1, x_1048);
return x_1049;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_5__getStructName___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_5__getStructName(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_4);
return x_5;
}
default: 
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_Syntax_prettyPrint(x_6);
x_8 = 0;
x_9 = l_Lean_Format_sbracket___closed__2;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l_Lean_Format_sbracket___closed__3;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
return x_12;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
return x_2;
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
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1() {
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
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1;
return x_1;
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
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = 0;
x_13 = l_Lean_Format_sbracket___closed__2;
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = l_Lean_Format_sbracket___closed__3;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_12);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_2);
x_18 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_4, x_2);
switch (lean_obj_tag(x_17)) {
case 0:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(x_19);
x_21 = 0;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_2);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
x_23 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_21);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(x_24);
x_26 = 0;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_26);
x_28 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_26);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = l_Lean_Syntax_prettyPrint(x_29);
x_31 = 0;
x_32 = l_Lean_Format_sbracket___closed__2;
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_31);
x_34 = l_Lean_Format_sbracket___closed__3;
x_35 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_31);
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_2);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_31);
x_37 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_18);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_31);
return x_37;
}
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" . ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatField___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<default>");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatField___closed__4() {
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = l_Lean_Elab_Term_StructInst_formatField___closed__2;
x_5 = l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(x_3, x_4);
x_6 = 0;
x_7 = l_Lean_formatEntry___closed__2;
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Syntax_prettyPrint(x_10);
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_6);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_6);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = l_Lean_Elab_Term_StructInst_formatField___closed__4;
x_17 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_6);
return x_17;
}
}
}
}
lean_object* _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct___main), 1, 0);
return x_1;
}
}
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object* x_1) {
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
x_6 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_7 = l_Lean_Elab_Term_StructInst_formatField(x_6, x_4);
x_8 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_5);
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
x_11 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
x_12 = l_Lean_Elab_Term_StructInst_formatField(x_11, x_9);
x_13 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_addParenHeuristic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentArray_Stats_toString___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" .. }");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Parser_Term_structInst___elambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(x_2);
x_5 = l_Lean_formatKVMap___closed__1;
x_6 = l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(x_4, x_5);
lean_dec(x_4);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = 0;
x_8 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_9 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*2, x_7);
x_10 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
x_11 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_7);
return x_11;
}
case 1:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
x_12 = 0;
x_13 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_14 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_12);
x_15 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4;
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_12);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_expr_dbg_to_string(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 0;
x_21 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
x_22 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_20);
x_23 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5;
x_24 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_20);
x_25 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_20);
x_26 = l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_20);
return x_27;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatStruct), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Struct_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_formatField), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_HasRepr___closed__1;
x_2 = l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
x_3 = lean_alloc_closure((void*)(l_Function_comp___rarg), 3, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_Field_hasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
return x_1;
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
x_8 = l_Lean_mkAppStx___closed__9;
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
x_19 = l_Lean_mkAppStx___closed__9;
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
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = 0;
x_11 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_10, x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
x_15 = lean_array_fset(x_8, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
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
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = l_Lean_Syntax_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
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
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Syntax_setArg(x_7, x_10, x_9);
x_12 = 1;
x_13 = l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(x_12, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Syntax_setArg(x_11, x_14, x_13);
x_16 = l_List_redLength___main___rarg(x_6);
x_17 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
x_18 = l_List_toArrayAux___main___rarg(x_6, x_17);
x_19 = x_18;
x_20 = l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(x_14, x_19);
x_21 = x_20;
x_22 = l_Lean_nullKind;
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_setArg(x_15, x_24, x_23);
return x_25;
}
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure syntax");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS(lean_object* x_1) {
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
x_9 = l_Lean_Syntax_isNatLitAux(x_8, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Syntax_getId(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
lean_dec(x_1);
x_19 = l_Lean_Syntax_isIdent(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_fieldIdxKind;
x_21 = l_Lean_Syntax_isNatLitAux(x_20, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_18);
x_22 = l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_Syntax_getId(x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Syntax_getKind(x_7);
x_9 = l_Lean_Parser_Term_structInstField___elambda__1___closed__2;
x_10 = lean_name_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
}
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
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
x_6 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_4);
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
x_11 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_5);
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
x_21 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_19);
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
x_26 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_20);
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Syntax_getArg(x_4, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_4, x_8);
x_10 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = l_Lean_Syntax_getArg(x_4, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_19 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_7);
lean_free_object(x_1);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_14);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_7);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_24);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_5);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(3u);
x_40 = l_Lean_Syntax_getArg(x_37, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_37, x_41);
x_43 = l___private_Lean_Elab_StructInst_6__toFieldLHS(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 1, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_unsigned_to_nat(1u);
x_49 = l_Lean_Syntax_getArg(x_37, x_48);
x_50 = l_Lean_Syntax_getArgs(x_49);
lean_dec(x_49);
x_51 = l_Array_toList___rarg(x_50);
lean_dec(x_50);
x_52 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(0, 1, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_40);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_37);
lean_ctor_set(x_60, 1, x_57);
lean_ctor_set(x_60, 2, x_58);
lean_ctor_set(x_60, 3, x_59);
x_61 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_38);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_62);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_65);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_7__mkStructView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArgs(x_5);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(x_6, x_7, x_7);
x_9 = l_Array_toList___rarg(x_8);
lean_dec(x_8);
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_3);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_2);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_3);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
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
x_3 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_3);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_6);
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
x_12 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object* x_1) {
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
x_6 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_5);
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
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_13 = x_7;
} else {
 lean_dec_ref(x_7);
 x_13 = lean_box(0);
}
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_24; 
lean_dec(x_23);
lean_free_object(x_1);
lean_dec(x_4);
x_24 = lean_box(0);
x_16 = x_24;
goto block_22;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
x_17 = l_Lean_Name_components(x_15);
x_18 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_14, x_17);
x_19 = l_List_append___rarg(x_18, x_12);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_11);
if (lean_is_scalar(x_13)) {
 x_21 = lean_alloc_ctor(1, 2, 0);
} else {
 x_21 = x_13;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_free_object(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_7, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_7, 0);
lean_dec(x_27);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
else
{
lean_object* x_28; 
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_6);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(x_30);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 3);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_39 = x_32;
} else {
 lean_dec_ref(x_32);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
if (lean_obj_tag(x_41) == 1)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_31);
return x_50;
}
else
{
lean_object* x_51; 
lean_dec(x_49);
lean_dec(x_29);
x_51 = lean_box(0);
x_42 = x_51;
goto block_48;
}
}
else
{
lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_29);
lean_ctor_set(x_52, 1, x_31);
return x_52;
}
block_48:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
x_43 = l_Lean_Name_components(x_41);
x_44 = l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(x_40, x_43);
x_45 = l_List_append___rarg(x_44, x_38);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
if (lean_is_scalar(x_39)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_39;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_31);
return x_47;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_53 = x_32;
} else {
 lean_dec_ref(x_32);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_29);
lean_ctor_set(x_54, 1, x_31);
return x_54;
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2), 1, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_3 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, structure has only #");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" fields");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field index, index must be greater than 0");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_25; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_9 = x_2;
} else {
 lean_dec_ref(x_2);
 x_9 = lean_box(0);
}
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 1)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 2);
x_30 = lean_ctor_get(x_7, 3);
x_31 = lean_ctor_get(x_7, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_25, 1);
x_34 = lean_ctor_get(x_25, 0);
lean_dec(x_34);
x_35 = !lean_is_exclusive(x_26);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_array_get_size(x_1);
x_41 = lean_nat_dec_lt(x_40, x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_sub(x_37, x_42);
lean_dec(x_37);
x_44 = l_Lean_Name_inhabited;
x_45 = lean_array_get(x_44, x_1, x_43);
lean_dec(x_43);
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_45);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_free_object(x_26);
lean_dec(x_37);
lean_free_object(x_25);
lean_dec(x_33);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_46 = l_Nat_repr(x_40);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_throwErrorAt___rarg(x_36, x_52, x_3, x_4);
lean_dec(x_36);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_free_object(x_26);
lean_dec(x_37);
lean_free_object(x_25);
lean_dec(x_33);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_58 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_59 = l_Lean_Elab_Term_throwErrorAt___rarg(x_36, x_58, x_3, x_4);
lean_dec(x_36);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_array_get_size(x_1);
x_69 = lean_nat_dec_lt(x_68, x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_sub(x_65, x_70);
lean_dec(x_65);
x_72 = l_Lean_Name_inhabited;
x_73 = lean_array_get(x_72, x_1, x_71);
lean_dec(x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_64);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_25, 0, x_74);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_65);
lean_free_object(x_25);
lean_dec(x_33);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_75 = l_Nat_repr(x_68);
x_76 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Term_throwErrorAt___rarg(x_64, x_81, x_3, x_4);
lean_dec(x_64);
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_65);
lean_free_object(x_25);
lean_dec(x_33);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_87 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_88 = l_Lean_Elab_Term_throwErrorAt___rarg(x_64, x_87, x_3, x_4);
lean_dec(x_64);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
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
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_93 = lean_ctor_get(x_25, 1);
lean_inc(x_93);
lean_dec(x_25);
x_94 = lean_ctor_get(x_26, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_26, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_96 = x_26;
} else {
 lean_dec_ref(x_26);
 x_96 = lean_box(0);
}
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_eq(x_95, x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_array_get_size(x_1);
x_100 = lean_nat_dec_lt(x_99, x_95);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_95, x_101);
lean_dec(x_95);
x_103 = l_Lean_Name_inhabited;
x_104 = lean_array_get(x_103, x_1, x_102);
lean_dec(x_102);
if (lean_is_scalar(x_96)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_96;
 lean_ctor_set_tag(x_105, 0);
}
lean_ctor_set(x_105, 0, x_94);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_93);
lean_ctor_set(x_7, 1, x_106);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_107 = l_Nat_repr(x_99);
x_108 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_111 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
x_112 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Elab_Term_throwErrorAt___rarg(x_94, x_113, x_3, x_4);
lean_dec(x_94);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
x_119 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_120 = l_Lean_Elab_Term_throwErrorAt___rarg(x_94, x_119, x_3, x_4);
lean_dec(x_94);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_ctor_get(x_7, 0);
x_126 = lean_ctor_get(x_7, 2);
x_127 = lean_ctor_get(x_7, 3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_7);
x_128 = lean_ctor_get(x_25, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_129 = x_25;
} else {
 lean_dec_ref(x_25);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_26, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_26, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_132 = x_26;
} else {
 lean_dec_ref(x_26);
 x_132 = lean_box(0);
}
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_nat_dec_eq(x_131, x_133);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_array_get_size(x_1);
x_136 = lean_nat_dec_lt(x_135, x_131);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_135);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_sub(x_131, x_137);
lean_dec(x_131);
x_139 = l_Lean_Name_inhabited;
x_140 = lean_array_get(x_139, x_1, x_138);
lean_dec(x_138);
if (lean_is_scalar(x_132)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_132;
 lean_ctor_set_tag(x_141, 0);
}
lean_ctor_set(x_141, 0, x_130);
lean_ctor_set(x_141, 1, x_140);
if (lean_is_scalar(x_129)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_129;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_128);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_125);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_126);
lean_ctor_set(x_143, 3, x_127);
x_10 = x_143;
x_11 = x_4;
goto block_24;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_9);
lean_dec(x_8);
x_144 = l_Nat_repr(x_135);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_148 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
x_149 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_Elab_Term_throwErrorAt___rarg(x_130, x_150, x_3, x_4);
lean_dec(x_130);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
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
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_9);
lean_dec(x_8);
x_156 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_157 = l_Lean_Elab_Term_throwErrorAt___rarg(x_130, x_156, x_3, x_4);
lean_dec(x_130);
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
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_dec(x_26);
lean_dec(x_25);
x_10 = x_7;
x_11 = x_4;
goto block_24;
}
}
block_24:
{
lean_object* x_12; 
x_12 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_8, x_3, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
if (lean_is_scalar(x_9)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_9;
}
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_14);
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
if (lean_is_scalar(x_9)) {
 x_18 = lean_alloc_ctor(1, 2, 0);
} else {
 x_18 = x_9;
}
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
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
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 2);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_apply_3(x_2, x_8, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_1, 2, x_12);
lean_ctor_set(x_10, 0, x_1);
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_1, 2, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 0);
x_18 = lean_ctor_get(x_10, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_10);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_apply_3(x_2, x_22, x_3, x_4);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_23);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
x_30 = lean_ctor_get(x_24, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_32 = x_24;
} else {
 lean_dec_ref(x_24);
 x_32 = lean_box(0);
}
if (lean_is_scalar(x_32)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_32;
}
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_9 = l_Lean_getStructureFields(x_6, x_8);
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_9, x_2, x_3, x_7);
lean_dec(x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_6);
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
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_dec(x_1);
x_12 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_13 = l_unreachable_x21___rarg(x_12);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_16 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_1, x_15);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_name_mk_string(x_18, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_1);
x_22 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_23 = l_unreachable_x21___rarg(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_16);
return x_24;
}
}
}
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a field of structure '");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to access field '");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' in parent structure");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_10 = x_3;
} else {
 lean_dec_ref(x_3);
 x_10 = lean_box(0);
}
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_33);
lean_inc(x_2);
x_34 = l_Lean_findField_x3f___main(x_2, x_33, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_35 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_36 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_33);
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
x_43 = l_Lean_Elab_Term_throwErrorAt___rarg(x_31, x_42, x_4, x_5);
lean_dec(x_31);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_34, 0);
lean_inc(x_48);
lean_dec(x_34);
x_49 = lean_name_eq(x_48, x_33);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_8);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_8, 3);
lean_dec(x_51);
x_52 = lean_ctor_get(x_8, 2);
lean_dec(x_52);
x_53 = lean_ctor_get(x_8, 1);
lean_dec(x_53);
x_54 = lean_ctor_get(x_8, 0);
lean_dec(x_54);
lean_inc(x_2);
x_55 = l_Lean_getPathToBaseStructure_x3f(x_2, x_48, x_33);
lean_dec(x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_free_object(x_8);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_56 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_56, 0, x_32);
x_57 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_60 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Elab_Term_throwErrorAt___rarg(x_31, x_60, x_4, x_5);
lean_dec(x_31);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_32);
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
lean_dec(x_55);
x_67 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_31, x_66);
x_68 = l_List_append___rarg(x_67, x_26);
lean_ctor_set(x_8, 1, x_68);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
else
{
lean_object* x_69; 
lean_dec(x_8);
lean_inc(x_2);
x_69 = l_Lean_getPathToBaseStructure_x3f(x_2, x_48, x_33);
lean_dec(x_48);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_32);
x_71 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_72 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Elab_Term_throwErrorAt___rarg(x_31, x_74, x_4, x_5);
lean_dec(x_31);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_32);
x_80 = lean_ctor_get(x_69, 0);
lean_inc(x_80);
lean_dec(x_69);
x_81 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_31, x_80);
x_82 = l_List_append___rarg(x_81, x_26);
x_83 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_83, 0, x_28);
lean_ctor_set(x_83, 1, x_82);
lean_ctor_set(x_83, 2, x_29);
lean_ctor_set(x_83, 3, x_30);
x_11 = x_83;
x_12 = x_5;
goto block_25;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
x_11 = x_8;
x_12 = x_5;
goto block_25;
}
}
block_25:
{
lean_object* x_13; 
x_13 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_9, x_4, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
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
if (lean_is_scalar(x_10)) {
 x_19 = lean_alloc_ctor(1, 2, 0);
} else {
 x_19 = x_10;
}
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_10);
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
}
}
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed), 5, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_7, x_2, x_6);
return x_8;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_7);
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
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_1, x_2, x_12);
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
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_10);
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
x_17 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_13, x_15);
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
x_18 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_10);
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
x_26 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_2, x_25);
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
x_32 = l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(x_28, x_30);
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
x_34 = l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has already beed specified");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_10 = l_unreachable_x21___rarg(x_9);
lean_inc(x_3);
x_11 = lean_apply_2(x_10, x_3, x_4);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_1 = x_12;
x_2 = x_8;
x_4 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
x_21 = lean_ctor_get(x_7, 1);
lean_dec(x_21);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_6);
x_26 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_26;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
lean_ctor_set(x_7, 1, x_28);
lean_ctor_set(x_7, 0, x_6);
x_29 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_29;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
x_32 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_6);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_ctor_set(x_7, 1, x_28);
lean_ctor_set(x_7, 0, x_6);
x_34 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_23, x_7);
x_1 = x_34;
x_2 = x_22;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_28);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_1);
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Term_throwErrorAt___rarg(x_36, x_41, x_3, x_4);
lean_dec(x_36);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_22);
lean_free_object(x_7);
lean_dec(x_1);
x_47 = lean_ctor_get(x_6, 0);
lean_inc(x_47);
lean_dec(x_6);
x_48 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_48, 0, x_23);
x_49 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Elab_Term_throwErrorAt___rarg(x_47, x_52, x_3, x_4);
lean_dec(x_47);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_7);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_1);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_60 = l_unreachable_x21___rarg(x_59);
lean_inc(x_3);
x_61 = lean_apply_2(x_60, x_3, x_4);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_1 = x_62;
x_2 = x_58;
x_4 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_58);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_7, 0);
lean_inc(x_69);
lean_dec(x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
lean_dec(x_2);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_6);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_74);
x_1 = x_75;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_72, 0);
lean_inc(x_77);
lean_dec(x_72);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_6);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_78);
x_1 = x_79;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_77, 0);
lean_inc(x_81);
x_82 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_6);
if (x_82 == 0)
{
uint8_t x_83; 
x_83 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_81);
lean_dec(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_77);
x_85 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_71, x_84);
x_1 = x_85;
x_2 = x_70;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_1);
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_88, 0, x_71);
x_89 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_92 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_Elab_Term_throwErrorAt___rarg(x_87, x_92, x_3, x_4);
lean_dec(x_87);
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
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_1);
x_98 = lean_ctor_get(x_6, 0);
lean_inc(x_98);
lean_dec(x_6);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_71);
x_100 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Term_throwErrorAt___rarg(x_98, x_103, x_3, x_4);
lean_dec(x_98);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_69);
lean_dec(x_6);
lean_dec(x_1);
x_109 = lean_ctor_get(x_2, 1);
lean_inc(x_109);
lean_dec(x_2);
x_110 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_111 = l_unreachable_x21___rarg(x_110);
lean_inc(x_3);
x_112 = lean_apply_2(x_111, x_3, x_4);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_1 = x_113;
x_2 = x_109;
x_4 = x_114;
goto _start;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
lean_dec(x_3);
x_116 = lean_ctor_get(x_112, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_112, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_118 = x_112;
} else {
 lean_dec_ref(x_112);
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
}
lean_object* _init_l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
x_5 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_name_eq(x_7, x_1);
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
lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a valid field of '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_3, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_9 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_PrettyPrinter_Parenthesizer_parenthesizerForKind___closed__5;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Term_throwError___rarg(x_16, x_4, x_5);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
return x_19;
}
}
}
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_Name_toString___closed__1;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2);
x_6 = l_Lean_Parser_declareBuiltinParser___closed__3;
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
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 2)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkProj(x_1, x_12, x_9);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_8, 1);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_fget(x_15, x_17);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_15, x_17, x_20);
x_22 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_19, x_3);
x_23 = lean_array_fset(x_21, x_17, x_22);
lean_ctor_set(x_8, 1, x_23);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_8, 0);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_8);
x_26 = lean_array_get_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_29);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_array_fget(x_25, x_27);
x_31 = lean_box(0);
x_32 = lean_array_fset(x_25, x_27, x_31);
x_33 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_30, x_3);
x_34 = lean_array_fset(x_32, x_27, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_24);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_35);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
}
else
{
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_10, 0, x_4);
return x_10;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = l_Lean_mkProj(x_1, x_36, x_9);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_41 = x_8;
} else {
 lean_dec_ref(x_8);
 x_41 = lean_box(0);
}
x_42 = lean_array_get_size(x_40);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
if (lean_is_scalar(x_41)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_41;
}
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_array_fget(x_40, x_43);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_40, x_43, x_48);
x_50 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_47, x_3);
x_51 = lean_array_fset(x_49, x_43, x_50);
if (lean_is_scalar(x_41)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_41;
}
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_37);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_3);
lean_ctor_set(x_4, 1, x_38);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_37);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_free_object(x_4);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_61 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = l_Lean_mkProj(x_1, x_62, x_60);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_59, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_68 = x_59;
} else {
 lean_dec_ref(x_59);
 x_68 = lean_box(0);
}
x_69 = lean_array_get_size(x_67);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_lt(x_70, x_69);
lean_dec(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
if (lean_is_scalar(x_68)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_68;
}
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_67);
x_73 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_64;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_63);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_array_fget(x_67, x_70);
x_76 = lean_box(0);
x_77 = lean_array_fset(x_67, x_70, x_76);
x_78 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_75, x_3);
x_79 = lean_array_fset(x_77, x_70, x_78);
if (lean_is_scalar(x_68)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_68;
}
lean_ctor_set(x_80, 0, x_66);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_64;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_63);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_3);
x_83 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_83, 0, x_59);
lean_ctor_set(x_83, 1, x_65);
if (lean_is_scalar(x_64)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_64;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_63);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_1);
x_85 = lean_ctor_get(x_61, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_61, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_87 = x_61;
} else {
 lean_dec_ref(x_61);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_4);
lean_ctor_set(x_89, 1, x_6);
return x_89;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object* x_1) {
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__1), 1, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Term_StructInst_Field_inhabited(lean_box(0));
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed), 2, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_inc(x_11);
x_14 = l_List_map___main___rarg(x_13, x_11);
x_15 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_8);
lean_inc(x_10);
lean_inc(x_2);
x_16 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_2, x_3, x_10, x_15, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_21 = l_List_head_x21___rarg(x_20, x_11);
lean_dec(x_11);
x_22 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_6);
x_23 = lean_unsigned_to_nat(4u);
x_24 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_25 = l_Lean_Syntax_setArg(x_5, x_23, x_24);
x_26 = l_List_redLength___main___rarg(x_14);
x_27 = lean_mk_empty_array_with_capacity(x_26);
lean_dec(x_26);
x_28 = l_List_toArrayAux___main___rarg(x_14, x_27);
x_29 = x_28;
x_30 = l_Id_monad;
x_31 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_umapMAux___main___rarg(x_30, lean_box(0), x_31, x_32, x_29);
x_34 = x_33;
x_35 = l_Lean_List_format___rarg___closed__2;
x_36 = l_Lean_mkAtomFrom(x_5, x_35);
lean_dec(x_5);
x_37 = l_Lean_mkSepStx(x_34, x_36);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(2u);
x_39 = l_Lean_Syntax_setArg(x_25, x_38, x_37);
x_40 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_39, x_18);
x_41 = !lean_is_exclusive(x_21);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_21, 1);
x_43 = lean_ctor_get(x_21, 2);
lean_dec(x_43);
x_44 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_45 = l_List_head_x21___rarg(x_44, x_42);
lean_dec(x_42);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_21, 2, x_48);
lean_ctor_set(x_21, 1, x_47);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_21, 0);
x_50 = lean_ctor_get(x_21, 1);
x_51 = lean_ctor_get(x_21, 3);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_21);
x_52 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_53 = l_List_head_x21___rarg(x_52, x_50);
lean_dec(x_50);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_40);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set(x_16, 0, x_57);
return x_16;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_free_object(x_16);
x_58 = lean_ctor_get(x_22, 0);
lean_inc(x_58);
lean_dec(x_22);
x_59 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_59, 0, x_5);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_14);
lean_ctor_set(x_59, 3, x_18);
x_60 = lean_apply_3(x_6, x_59, x_8, x_19);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_21);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_21, 1);
x_65 = lean_ctor_get(x_21, 2);
lean_dec(x_65);
x_66 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_67 = l_List_head_x21___rarg(x_66, x_64);
lean_dec(x_64);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_21, 2, x_70);
lean_ctor_set(x_21, 1, x_69);
lean_ctor_set(x_60, 0, x_21);
return x_60;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_60, 0);
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
x_74 = lean_ctor_get(x_21, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
x_75 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_76 = l_List_head_x21___rarg(x_75, x_73);
lean_dec(x_73);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_71);
x_80 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_80, 0, x_72);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
lean_ctor_set(x_80, 3, x_74);
lean_ctor_set(x_60, 0, x_80);
return x_60;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_60, 0);
x_82 = lean_ctor_get(x_60, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_60);
x_83 = lean_ctor_get(x_21, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_21, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_21, 3);
lean_inc(x_85);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 lean_ctor_release(x_21, 2);
 lean_ctor_release(x_21, 3);
 x_86 = x_21;
} else {
 lean_dec_ref(x_21);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_88 = l_List_head_x21___rarg(x_87, x_84);
lean_dec(x_84);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_81);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 4, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_85);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_82);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_21);
x_94 = !lean_is_exclusive(x_60);
if (x_94 == 0)
{
return x_60;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_60, 0);
x_96 = lean_ctor_get(x_60, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_60);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_16, 0);
x_99 = lean_ctor_get(x_16, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_16);
x_100 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_101 = l_List_head_x21___rarg(x_100, x_11);
lean_dec(x_11);
x_102 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_10);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_8);
lean_dec(x_6);
x_103 = lean_unsigned_to_nat(4u);
x_104 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_105 = l_Lean_Syntax_setArg(x_5, x_103, x_104);
x_106 = l_List_redLength___main___rarg(x_14);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_dec(x_106);
x_108 = l_List_toArrayAux___main___rarg(x_14, x_107);
x_109 = x_108;
x_110 = l_Id_monad;
x_111 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Array_umapMAux___main___rarg(x_110, lean_box(0), x_111, x_112, x_109);
x_114 = x_113;
x_115 = l_Lean_List_format___rarg___closed__2;
x_116 = l_Lean_mkAtomFrom(x_5, x_115);
lean_dec(x_5);
x_117 = l_Lean_mkSepStx(x_114, x_116);
lean_dec(x_114);
x_118 = lean_unsigned_to_nat(2u);
x_119 = l_Lean_Syntax_setArg(x_105, x_118, x_117);
x_120 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_119, x_98);
x_121 = lean_ctor_get(x_101, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_101, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_101, 3);
lean_inc(x_123);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 x_124 = x_101;
} else {
 lean_dec_ref(x_101);
 x_124 = lean_box(0);
}
x_125 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_126 = l_List_head_x21___rarg(x_125, x_122);
lean_dec(x_122);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_120);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 4, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_121);
lean_ctor_set(x_130, 1, x_128);
lean_ctor_set(x_130, 2, x_129);
lean_ctor_set(x_130, 3, x_123);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_99);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_102, 0);
lean_inc(x_132);
lean_dec(x_102);
x_133 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_133, 0, x_5);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_133, 2, x_14);
lean_ctor_set(x_133, 3, x_98);
x_134 = lean_apply_3(x_6, x_133, x_8, x_99);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
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
x_138 = lean_ctor_get(x_101, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_101, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_101, 3);
lean_inc(x_140);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 lean_ctor_release(x_101, 2);
 lean_ctor_release(x_101, 3);
 x_141 = x_101;
} else {
 lean_dec_ref(x_101);
 x_141 = lean_box(0);
}
x_142 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_143 = l_List_head_x21___rarg(x_142, x_139);
lean_dec(x_139);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_135);
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(0, 4, 0);
} else {
 x_147 = x_141;
}
lean_ctor_set(x_147, 0, x_138);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_146);
lean_ctor_set(x_147, 3, x_140);
if (lean_is_scalar(x_137)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_137;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_136);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_101);
x_149 = lean_ctor_get(x_134, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_134, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_16);
if (x_153 == 0)
{
return x_16;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_16, 0);
x_155 = lean_ctor_get(x_16, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_16);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_157 = lean_ctor_get(x_12, 0);
lean_inc(x_157);
lean_dec(x_12);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_9);
return x_158;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
x_11 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed), 9, 6);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
x_15 = l_Std_HashMap_toList___rarg(x_12);
lean_dec(x_12);
x_16 = l_List_mapM___main___rarg(x_7, lean_box(0), lean_box(0), x_14, x_15);
x_17 = lean_apply_2(x_16, x_9, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_getStructureFields(x_6, x_8);
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
x_11 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
lean_inc(x_10);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__4), 10, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_9);
lean_closure_set(x_12, 3, x_6);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_1);
lean_closure_set(x_12, 6, x_11);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_3, 9);
x_15 = l_Lean_Elab_replaceRef(x_10, x_14);
lean_dec(x_14);
lean_dec(x_10);
lean_ctor_set(x_3, 9, x_15);
x_16 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_11, x_2, x_12);
x_17 = lean_apply_2(x_16, x_3, x_7);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_3, 2);
x_21 = lean_ctor_get(x_3, 3);
x_22 = lean_ctor_get(x_3, 4);
x_23 = lean_ctor_get(x_3, 5);
x_24 = lean_ctor_get(x_3, 6);
x_25 = lean_ctor_get(x_3, 7);
x_26 = lean_ctor_get(x_3, 8);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_28 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_29 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_30 = lean_ctor_get(x_3, 9);
lean_inc(x_30);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_31 = l_Lean_Elab_replaceRef(x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_23);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_26);
lean_ctor_set(x_32, 9, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*10, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 1, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 2, x_29);
x_33 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_11, x_2, x_12);
x_34 = lean_apply_2(x_33, x_32, x_7);
return x_34;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
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
x_4 = l_List_find_x3f___main___rarg(x_3, x_1);
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
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_9);
x_14 = l_Lean_Elab_Term_StructInst_findField_x3f(x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_9);
lean_inc(x_3);
x_15 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_16 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_box(2);
lean_inc(x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_5);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_17);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_16);
x_24 = l_Lean_mkHole(x_4);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_inc(x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_10);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_32, x_33);
lean_dec(x_32);
x_35 = l_Lean_Syntax_getArg(x_34, x_33);
lean_dec(x_34);
lean_inc(x_9);
x_36 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_35, x_9);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_9);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_10);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_12);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_9);
x_46 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_6, x_9, x_45, x_11, x_12);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_5);
lean_inc(x_4);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_5);
lean_ctor_set(x_49, 3, x_47);
x_50 = lean_apply_3(x_7, x_49, x_11, x_48);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_4);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_5);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_55);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_10);
lean_ctor_set(x_50, 0, x_58);
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
lean_inc(x_4);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_9);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_5);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_61);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_10);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
else
{
uint8_t x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_50);
if (x_68 == 0)
{
return x_50;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_50, 0);
x_70 = lean_ctor_get(x_50, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_50);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_44);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_46);
if (x_72 == 0)
{
return x_46;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_46, 0);
x_74 = lean_ctor_get(x_46, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_46);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = lean_ctor_get(x_14, 0);
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_10);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_12);
return x_78;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_StructInst_Struct_structName(x_2);
lean_inc(x_8);
lean_inc(x_6);
x_9 = l_Lean_getStructureFields(x_6, x_8);
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_2);
x_11 = lean_box(0);
lean_inc(x_9);
lean_inc(x_10);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed), 12, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_6);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_9);
lean_closure_set(x_12, 6, x_1);
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_3, 9);
x_15 = l_Lean_Elab_replaceRef(x_10, x_14);
lean_dec(x_14);
lean_dec(x_10);
lean_ctor_set(x_3, 9, x_15);
x_16 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_iterateMAux___main___rarg(x_16, lean_box(0), x_9, x_12, x_17, x_11);
x_19 = lean_apply_2(x_18, x_3, x_7);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_List_reverse___rarg(x_21);
x_23 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = l_List_reverse___rarg(x_24);
x_27 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = lean_ctor_get(x_3, 4);
x_38 = lean_ctor_get(x_3, 5);
x_39 = lean_ctor_get(x_3, 6);
x_40 = lean_ctor_get(x_3, 7);
x_41 = lean_ctor_get(x_3, 8);
x_42 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_43 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_45 = lean_ctor_get(x_3, 9);
lean_inc(x_45);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_46 = l_Lean_Elab_replaceRef(x_10, x_45);
lean_dec(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_47, 2, x_35);
lean_ctor_set(x_47, 3, x_36);
lean_ctor_set(x_47, 4, x_37);
lean_ctor_set(x_47, 5, x_38);
lean_ctor_set(x_47, 6, x_39);
lean_ctor_set(x_47, 7, x_40);
lean_ctor_set(x_47, 8, x_41);
lean_ctor_set(x_47, 9, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*10, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 1, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*10 + 2, x_44);
x_48 = l_Lean_MetavarContext_MkBinding_mkBinding___closed__1;
x_49 = lean_unsigned_to_nat(0u);
x_50 = l_Array_iterateMAux___main___rarg(x_48, lean_box(0), x_9, x_12, x_49, x_11);
x_51 = lean_apply_2(x_50, x_47, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_54 = x_51;
} else {
 lean_dec_ref(x_51);
 x_54 = lean_box(0);
}
x_55 = l_List_reverse___rarg(x_52);
x_56 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_55);
if (lean_is_scalar(x_54)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_54;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_2);
x_58 = lean_ctor_get(x_51, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_6);
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
x_17 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_10);
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
x_27 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_3 = l_List_head_x21___rarg___closed__2;
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
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_Elab_Term_StructInst_Field_toSyntax(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
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
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_15);
x_17 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_15);
x_18 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_14);
lean_inc(x_3);
x_19 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_14, x_18, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_15);
lean_dec(x_15);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_unsigned_to_nat(4u);
x_25 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_26 = l_Lean_Syntax_setArg(x_5, x_24, x_25);
x_27 = l_List_redLength___main___rarg(x_17);
x_28 = lean_mk_empty_array_with_capacity(x_27);
lean_dec(x_27);
x_29 = l_List_toArrayAux___main___rarg(x_17, x_28);
x_30 = x_29;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_31, x_30);
x_33 = x_32;
x_34 = l_Lean_List_format___rarg___closed__2;
x_35 = l_Lean_mkAtomFrom(x_5, x_34);
x_36 = l_Lean_mkSepStx(x_33, x_35);
lean_dec(x_33);
x_37 = lean_unsigned_to_nat(2u);
x_38 = l_Lean_Syntax_setArg(x_26, x_37, x_36);
x_39 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_38, x_20);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_22, 1);
x_42 = lean_ctor_get(x_22, 2);
lean_dec(x_42);
x_43 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_41);
lean_dec(x_41);
x_44 = lean_box(0);
lean_ctor_set(x_6, 1, x_44);
lean_ctor_set(x_6, 0, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_22, 2, x_45);
lean_ctor_set(x_22, 1, x_6);
x_46 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_21);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_48);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_22);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_22);
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_22, 0);
x_59 = lean_ctor_get(x_22, 1);
x_60 = lean_ctor_get(x_22, 3);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_22);
x_61 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_59);
lean_dec(x_59);
x_62 = lean_box(0);
lean_ctor_set(x_6, 1, x_62);
lean_ctor_set(x_6, 0, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_39);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_6);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set(x_64, 3, x_60);
x_65 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_21);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
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
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_23, 0);
lean_inc(x_75);
lean_dec(x_23);
lean_inc(x_5);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_5);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_17);
lean_ctor_set(x_76, 3, x_20);
lean_inc(x_7);
x_77 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_76, x_7, x_21);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = !lean_is_exclusive(x_22);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_ctor_get(x_22, 1);
x_82 = lean_ctor_get(x_22, 2);
lean_dec(x_82);
x_83 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_81);
lean_dec(x_81);
x_84 = lean_box(0);
lean_ctor_set(x_6, 1, x_84);
lean_ctor_set(x_6, 0, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_22, 2, x_85);
lean_ctor_set(x_22, 1, x_6);
x_86 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_79);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_22);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_86, 0, x_89);
return x_86;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_86, 0);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_86);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_22);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_22);
x_94 = !lean_is_exclusive(x_86);
if (x_94 == 0)
{
return x_86;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_86, 0);
x_96 = lean_ctor_get(x_86, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_86);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_22, 0);
x_99 = lean_ctor_get(x_22, 1);
x_100 = lean_ctor_get(x_22, 3);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_22);
x_101 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_99);
lean_dec(x_99);
x_102 = lean_box(0);
lean_ctor_set(x_6, 1, x_102);
lean_ctor_set(x_6, 0, x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_78);
x_104 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_6);
lean_ctor_set(x_104, 2, x_103);
lean_ctor_set(x_104, 3, x_100);
x_105 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_79);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_106);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_104);
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_113 = x_105;
} else {
 lean_dec_ref(x_105);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_22);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_77);
if (x_115 == 0)
{
return x_77;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_77, 0);
x_117 = lean_ctor_get(x_77, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_77);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_free_object(x_6);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_119 = !lean_is_exclusive(x_19);
if (x_119 == 0)
{
return x_19;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_19, 0);
x_121 = lean_ctor_get(x_19, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_19);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_15);
lean_dec(x_14);
x_123 = lean_ctor_get(x_16, 0);
lean_inc(x_123);
lean_dec(x_16);
x_124 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8);
if (lean_obj_tag(x_124) == 0)
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_124, 0);
lean_ctor_set(x_6, 1, x_126);
lean_ctor_set(x_6, 0, x_123);
lean_ctor_set(x_124, 0, x_6);
return x_124;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_124, 0);
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_124);
lean_ctor_set(x_6, 1, x_127);
lean_ctor_set(x_6, 0, x_123);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_6);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_123);
lean_free_object(x_6);
x_130 = !lean_is_exclusive(x_124);
if (x_130 == 0)
{
return x_124;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_124, 0);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_124);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_6, 0);
x_135 = lean_ctor_get(x_6, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_6);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_inc(x_137);
x_139 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_137);
x_140 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_136);
lean_inc(x_3);
x_141 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_136, x_140, x_7, x_8);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_137);
lean_dec(x_137);
lean_inc(x_3);
lean_inc(x_2);
x_145 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_136);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_146 = lean_unsigned_to_nat(4u);
x_147 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_148 = l_Lean_Syntax_setArg(x_5, x_146, x_147);
x_149 = l_List_redLength___main___rarg(x_139);
x_150 = lean_mk_empty_array_with_capacity(x_149);
lean_dec(x_149);
x_151 = l_List_toArrayAux___main___rarg(x_139, x_150);
x_152 = x_151;
x_153 = lean_unsigned_to_nat(0u);
x_154 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_153, x_152);
x_155 = x_154;
x_156 = l_Lean_List_format___rarg___closed__2;
x_157 = l_Lean_mkAtomFrom(x_5, x_156);
x_158 = l_Lean_mkSepStx(x_155, x_157);
lean_dec(x_155);
x_159 = lean_unsigned_to_nat(2u);
x_160 = l_Lean_Syntax_setArg(x_148, x_159, x_158);
x_161 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_160, x_142);
x_162 = lean_ctor_get(x_144, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_144, 3);
lean_inc(x_164);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 x_165 = x_144;
} else {
 lean_dec_ref(x_144);
 x_165 = lean_box(0);
}
x_166 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_163);
lean_dec(x_163);
x_167 = lean_box(0);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_169, 0, x_161);
if (lean_is_scalar(x_165)) {
 x_170 = lean_alloc_ctor(0, 4, 0);
} else {
 x_170 = x_165;
}
lean_ctor_set(x_170, 0, x_162);
lean_ctor_set(x_170, 1, x_168);
lean_ctor_set(x_170, 2, x_169);
lean_ctor_set(x_170, 3, x_164);
x_171 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_135, x_7, x_143);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_174 = x_171;
} else {
 lean_dec_ref(x_171);
 x_174 = lean_box(0);
}
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_172);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_170);
x_177 = lean_ctor_get(x_171, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_171, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_179 = x_171;
} else {
 lean_dec_ref(x_171);
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
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_145, 0);
lean_inc(x_181);
lean_dec(x_145);
lean_inc(x_5);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_5);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_182, 2, x_139);
lean_ctor_set(x_182, 3, x_142);
lean_inc(x_7);
x_183 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_182, x_7, x_143);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_144, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_144, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_144, 3);
lean_inc(x_188);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 lean_ctor_release(x_144, 2);
 lean_ctor_release(x_144, 3);
 x_189 = x_144;
} else {
 lean_dec_ref(x_144);
 x_189 = lean_box(0);
}
x_190 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_187);
lean_dec(x_187);
x_191 = lean_box(0);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_184);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(0, 4, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_186);
lean_ctor_set(x_194, 1, x_192);
lean_ctor_set(x_194, 2, x_193);
lean_ctor_set(x_194, 3, x_188);
x_195 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_135, x_7, x_185);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_196);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_194);
x_201 = lean_ctor_get(x_195, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_195, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_203 = x_195;
} else {
 lean_dec_ref(x_195);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_144);
lean_dec(x_135);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_183, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_183, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_207 = x_183;
} else {
 lean_dec_ref(x_183);
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
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_209 = lean_ctor_get(x_141, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_141, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_211 = x_141;
} else {
 lean_dec_ref(x_141);
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
lean_object* x_213; lean_object* x_214; 
lean_dec(x_137);
lean_dec(x_136);
x_213 = lean_ctor_get(x_138, 0);
lean_inc(x_213);
lean_dec(x_138);
x_214 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_135, x_7, x_8);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_217 = x_214;
} else {
 lean_dec_ref(x_214);
 x_217 = lean_box(0);
}
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set(x_218, 1, x_215);
if (lean_is_scalar(x_217)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_217;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_216);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_213);
x_220 = lean_ctor_get(x_214, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_214, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_222 = x_214;
} else {
 lean_dec_ref(x_214);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(x_10);
lean_dec(x_10);
x_13 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_7);
lean_inc(x_5);
x_8 = l_Lean_getStructureFields(x_5, x_7);
x_9 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed), 8, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_7);
lean_closure_set(x_10, 3, x_8);
lean_closure_set(x_10, 4, x_9);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 9);
x_13 = l_Lean_Elab_replaceRef(x_9, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_ctor_set(x_2, 9, x_13);
x_14 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_10, x_2, x_6);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = lean_ctor_get(x_2, 3);
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_ctor_get(x_2, 5);
x_21 = lean_ctor_get(x_2, 6);
x_22 = lean_ctor_get(x_2, 7);
x_23 = lean_ctor_get(x_2, 8);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_2, 9);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_28 = l_Lean_Elab_replaceRef(x_9, x_27);
lean_dec(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_20);
lean_ctor_set(x_29, 6, x_21);
lean_ctor_set(x_29, 7, x_22);
lean_ctor_set(x_29, 8, x_23);
lean_ctor_set(x_29, 9, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 2, x_26);
x_30 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_10, x_29, x_6);
return x_30;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_7);
x_13 = lean_nat_dec_lt(x_8, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_7, x_8);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_8, x_16);
lean_dec(x_8);
x_18 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_15);
x_19 = l_Lean_Elab_Term_StructInst_findField_x3f(x_18, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_inc(x_15);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_box(2);
lean_inc(x_5);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_15);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
lean_inc(x_5);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_9);
x_8 = x_17;
x_9 = x_28;
goto _start;
}
case 1:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_21);
x_30 = l_Lean_mkHole(x_5);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_inc(x_5);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_15);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_box(0);
lean_inc(x_5);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_31);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_9);
x_8 = x_17;
x_9 = x_37;
goto _start;
}
default: 
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_39, x_40);
lean_dec(x_39);
x_42 = l_Lean_Syntax_getArg(x_41, x_40);
lean_dec(x_41);
lean_inc(x_15);
x_43 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_42, x_15);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_5);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_15);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
lean_inc(x_5);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_9);
x_8 = x_17;
x_9 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
lean_inc(x_52);
lean_dec(x_20);
x_53 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_10);
lean_inc(x_15);
lean_inc(x_3);
x_54 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_15, x_53, x_10, x_11);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_6);
lean_inc(x_5);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_6);
lean_ctor_set(x_57, 3, x_55);
lean_inc(x_10);
x_58 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_57, x_10, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_59);
lean_inc(x_5);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_15);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_box(0);
lean_inc(x_5);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_5);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_61);
lean_ctor_set(x_66, 3, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_9);
x_8 = x_17;
x_9 = x_67;
x_11 = x_60;
goto _start;
}
else
{
uint8_t x_69; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_58);
if (x_69 == 0)
{
return x_58;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_58, 0);
x_71 = lean_ctor_get(x_58, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_58);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_52);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_54);
if (x_73 == 0)
{
return x_54;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_54, 0);
x_75 = lean_ctor_get(x_54, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_54);
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
lean_object* x_77; lean_object* x_78; 
lean_dec(x_15);
x_77 = lean_ctor_get(x_19, 0);
lean_inc(x_77);
lean_dec(x_19);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_9);
x_8 = x_17;
x_9 = x_78;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_7);
lean_inc(x_5);
x_8 = l_Lean_getStructureFields(x_5, x_7);
x_9 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_10 = lean_box(0);
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 9);
x_13 = l_Lean_Elab_replaceRef(x_9, x_12);
lean_dec(x_12);
lean_ctor_set(x_2, 9, x_13);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_5, x_7, x_8, x_9, x_10, x_8, x_14, x_10, x_2, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_List_reverse___rarg(x_17);
x_19 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = l_List_reverse___rarg(x_20);
x_23 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_ctor_get(x_2, 4);
x_34 = lean_ctor_get(x_2, 5);
x_35 = lean_ctor_get(x_2, 6);
x_36 = lean_ctor_get(x_2, 7);
x_37 = lean_ctor_get(x_2, 8);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_39 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_40 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_41 = lean_ctor_get(x_2, 9);
lean_inc(x_41);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_42 = l_Lean_Elab_replaceRef(x_9, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_30);
lean_ctor_set(x_43, 2, x_31);
lean_ctor_set(x_43, 3, x_32);
lean_ctor_set(x_43, 4, x_33);
lean_ctor_set(x_43, 5, x_34);
lean_ctor_set(x_43, 6, x_35);
lean_ctor_set(x_43, 7, x_36);
lean_ctor_set(x_43, 8, x_37);
lean_ctor_set(x_43, 9, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_38);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_39);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 2, x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_5, x_7, x_8, x_9, x_10, x_8, x_44, x_10, x_43, x_6);
lean_dec(x_8);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
x_49 = l_List_reverse___rarg(x_46);
x_50 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_49);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_48;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_54 = x_45;
} else {
 lean_dec_ref(x_45);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_5 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_4);
lean_inc(x_2);
x_6 = l___private_Lean_Elab_StructInst_9__expandNumLitFields(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_StructInst_10__expandParentFields(x_7, x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(x_10, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(x_13, x_2, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
return x_6;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_1, x_9);
lean_dec(x_1);
lean_inc(x_5);
x_11 = l_Lean_Elab_Term_whnfForall(x_2, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 7)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint8_t x_28; lean_object* x_29; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_12, sizeof(void*)*3);
lean_dec(x_12);
x_28 = (uint8_t)((x_16 << 24) >> 61);
x_29 = lean_box(x_28);
if (lean_obj_tag(x_29) == 3)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_14);
x_31 = 1;
x_32 = lean_box(0);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_mkFreshExprMVar(x_30, x_31, x_32, x_5, x_13);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_expr_instantiate1(x_15, x_34);
lean_dec(x_15);
lean_inc(x_34);
x_37 = l_Lean_mkApp(x_3, x_34);
x_38 = l_Lean_Expr_mvarId_x21(x_34);
lean_dec(x_34);
x_39 = lean_array_push(x_4, x_38);
x_1 = x_10;
x_2 = x_36;
x_3 = x_37;
x_4 = x_39;
x_6 = x_35;
goto _start;
}
else
{
lean_object* x_41; 
lean_dec(x_29);
x_41 = lean_box(0);
x_17 = x_41;
goto block_27;
}
block_27:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_mkFreshExprMVar(x_18, x_19, x_20, x_5, x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_expr_instantiate1(x_15, x_22);
lean_dec(x_15);
x_25 = l_Lean_mkApp(x_3, x_22);
x_1 = x_10;
x_2 = x_24;
x_3 = x_25;
x_6 = x_23;
goto _start;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_dec(x_11);
x_43 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_44 = l_Lean_Elab_Term_throwError___rarg(x_43, x_5, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_11);
if (x_45 == 0)
{
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_11, 0);
x_47 = lean_ctor_get(x_11, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_2);
lean_ctor_set(x_49, 2, x_4);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_6);
return x_50;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody___main(lean_object* x_1, lean_object* x_2) {
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
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_StructInst_21__getForallBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = l___private_Lean_Elab_StructInst_21__getForallBody___main(x_2, x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Expr_hasLooseBVars(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Elab_Term_isDefEq(x_8, x_12, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_4);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_inc(x_2);
x_9 = l_Lean_Elab_Term_mkFreshLevelMVar(x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_7, x_2, x_11);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_2);
x_19 = l_Lean_Elab_Term_mkFreshLevelMVar(x_2, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_18, x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_inc(x_3);
x_7 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_6, x_3, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_8);
x_11 = l_Lean_mkConst(x_10, x_8);
lean_inc(x_1);
x_12 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_instantiate_type_lparams(x_12, x_8);
lean_dec(x_8);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = l_Array_empty___closed__1;
lean_inc(x_3);
x_16 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_14, x_13, x_11, x_15, x_3, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_19, x_20, x_2, x_3, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_21, x_24, x_3, x_23);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_17);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_17);
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
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_3);
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
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstDefault");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2() {
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
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to elaborate field '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' of '");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
x_8 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_2);
x_12 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_14 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_16 = l_Lean_Elab_Term_throwError___rarg(x_15, x_4, x_5);
return x_16;
}
}
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg), 5, 0);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected unexpanded structure field");
return x_1;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_19; lean_object* x_24; lean_object* x_25; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_19 = x_26;
goto block_23;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_24, 0);
x_35 = lean_ctor_get(x_24, 1);
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 2);
x_38 = lean_ctor_get(x_8, 3);
lean_dec(x_38);
x_39 = lean_ctor_get(x_8, 1);
lean_dec(x_39);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
lean_inc(x_4);
x_41 = l_Lean_Elab_Term_whnfForall(x_34, x_4, x_5);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 7)
{
lean_dec(x_40);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 2);
lean_inc(x_67);
lean_dec(x_42);
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
x_70 = 1;
lean_inc(x_4);
lean_inc(x_69);
lean_inc(x_68);
x_71 = l_Lean_Elab_Term_elabTerm(x_68, x_69, x_70, x_4, x_43);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_4, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_4, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_4, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_4, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_4, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_4, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_4, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_4, 7);
lean_inc(x_81);
x_82 = lean_ctor_get(x_4, 8);
lean_inc(x_82);
x_83 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_84 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_85 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_86 = lean_ctor_get(x_4, 9);
lean_inc(x_86);
x_87 = l_Lean_Elab_replaceRef(x_68, x_86);
lean_dec(x_86);
lean_dec(x_68);
x_88 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_88, 2, x_76);
lean_ctor_set(x_88, 3, x_77);
lean_ctor_set(x_88, 4, x_78);
lean_ctor_set(x_88, 5, x_79);
lean_ctor_set(x_88, 6, x_80);
lean_ctor_set(x_88, 7, x_81);
lean_ctor_set(x_88, 8, x_82);
lean_ctor_set(x_88, 9, x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*10, x_83);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 1, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*10 + 2, x_85);
x_89 = l_Lean_Elab_Term_ensureHasType(x_69, x_72, x_88, x_73);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
x_92 = l_Lean_mkApp(x_30, x_91);
x_93 = lean_expr_instantiate1(x_67, x_91);
lean_dec(x_67);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_8, 3, x_94);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_93);
lean_ctor_set(x_2, 0, x_92);
lean_ctor_set(x_89, 0, x_2);
x_10 = x_89;
goto block_18;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_89, 0);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_89);
lean_inc(x_95);
x_97 = l_Lean_mkApp(x_30, x_95);
x_98 = lean_expr_instantiate1(x_67, x_95);
lean_dec(x_67);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_95);
lean_ctor_set(x_8, 3, x_99);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_98);
lean_ctor_set(x_2, 0, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_96);
x_10 = x_100;
goto block_18;
}
}
else
{
uint8_t x_101; 
lean_dec(x_67);
lean_free_object(x_8);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_101 = !lean_is_exclusive(x_89);
if (x_101 == 0)
{
x_10 = x_89;
goto block_18;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_89, 0);
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_89);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_10 = x_104;
goto block_18;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_8);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_105 = !lean_is_exclusive(x_71);
if (x_105 == 0)
{
x_10 = x_71;
goto block_18;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_71, 0);
x_107 = lean_ctor_get(x_71, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_71);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_10 = x_108;
goto block_18;
}
}
}
case 1:
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_free_object(x_2);
x_109 = lean_ctor_get(x_42, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_42, 2);
lean_inc(x_110);
lean_dec(x_42);
x_111 = !lean_is_exclusive(x_37);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_37, 0);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_109);
lean_inc(x_4);
lean_inc(x_113);
x_114 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_112, x_113, x_4, x_43);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = !lean_is_exclusive(x_115);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_115, 0);
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_4);
x_120 = l_Lean_Elab_Term_ensureHasType(x_113, x_118, x_4, x_116);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_120, 0);
lean_ctor_set(x_37, 0, x_119);
lean_inc(x_122);
x_123 = l_Lean_mkApp(x_30, x_122);
x_124 = lean_expr_instantiate1(x_110, x_122);
lean_dec(x_110);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_8, 3, x_125);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 0, x_124);
lean_ctor_set(x_24, 1, x_115);
lean_ctor_set(x_24, 0, x_123);
lean_ctor_set(x_120, 0, x_24);
x_10 = x_120;
goto block_18;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_126 = lean_ctor_get(x_120, 0);
x_127 = lean_ctor_get(x_120, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_120);
lean_ctor_set(x_37, 0, x_119);
lean_inc(x_126);
x_128 = l_Lean_mkApp(x_30, x_126);
x_129 = lean_expr_instantiate1(x_110, x_126);
lean_dec(x_110);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_8, 3, x_130);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 0, x_129);
lean_ctor_set(x_24, 1, x_115);
lean_ctor_set(x_24, 0, x_128);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_24);
lean_ctor_set(x_131, 1, x_127);
x_10 = x_131;
goto block_18;
}
}
else
{
uint8_t x_132; 
lean_free_object(x_115);
lean_dec(x_119);
lean_free_object(x_37);
lean_dec(x_110);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_132 = !lean_is_exclusive(x_120);
if (x_132 == 0)
{
x_10 = x_120;
goto block_18;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_120, 0);
x_134 = lean_ctor_get(x_120, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_120);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_10 = x_135;
goto block_18;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_115, 0);
x_137 = lean_ctor_get(x_115, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_115);
lean_inc(x_4);
x_138 = l_Lean_Elab_Term_ensureHasType(x_113, x_136, x_4, x_116);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
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
lean_ctor_set(x_37, 0, x_137);
lean_inc(x_139);
x_142 = l_Lean_mkApp(x_30, x_139);
x_143 = lean_expr_instantiate1(x_110, x_139);
lean_dec(x_110);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_8, 3, x_144);
lean_ctor_set(x_3, 1, x_35);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_3);
lean_ctor_set(x_24, 1, x_145);
lean_ctor_set(x_24, 0, x_142);
if (lean_is_scalar(x_141)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_141;
}
lean_ctor_set(x_146, 0, x_24);
lean_ctor_set(x_146, 1, x_140);
x_10 = x_146;
goto block_18;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_137);
lean_free_object(x_37);
lean_dec(x_110);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_147 = lean_ctor_get(x_138, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_138, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_149 = x_138;
} else {
 lean_dec_ref(x_138);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
x_10 = x_150;
goto block_18;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_113);
lean_free_object(x_37);
lean_dec(x_110);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_151 = !lean_is_exclusive(x_114);
if (x_151 == 0)
{
x_10 = x_114;
goto block_18;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_114, 0);
x_153 = lean_ctor_get(x_114, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_114);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_10 = x_154;
goto block_18;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_37, 0);
lean_inc(x_155);
lean_dec(x_37);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_109);
lean_inc(x_4);
lean_inc(x_156);
x_157 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_155, x_156, x_4, x_43);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_162 = x_158;
} else {
 lean_dec_ref(x_158);
 x_162 = lean_box(0);
}
lean_inc(x_4);
x_163 = l_Lean_Elab_Term_ensureHasType(x_156, x_160, x_4, x_159);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_161);
lean_inc(x_164);
x_168 = l_Lean_mkApp(x_30, x_164);
x_169 = lean_expr_instantiate1(x_110, x_164);
lean_dec(x_110);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_164);
lean_ctor_set(x_8, 3, x_170);
lean_ctor_set(x_8, 2, x_167);
lean_ctor_set(x_3, 1, x_35);
if (lean_is_scalar(x_162)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_162;
}
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_3);
lean_ctor_set(x_24, 1, x_171);
lean_ctor_set(x_24, 0, x_168);
if (lean_is_scalar(x_166)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_166;
}
lean_ctor_set(x_172, 0, x_24);
lean_ctor_set(x_172, 1, x_165);
x_10 = x_172;
goto block_18;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_110);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_173 = lean_ctor_get(x_163, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_163, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_175 = x_163;
} else {
 lean_dec_ref(x_163);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
x_10 = x_176;
goto block_18;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_156);
lean_dec(x_110);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_177 = lean_ctor_get(x_157, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_157, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_179 = x_157;
} else {
 lean_dec_ref(x_157);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
x_10 = x_180;
goto block_18;
}
}
}
default: 
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_181 = lean_ctor_get(x_42, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_42, 2);
lean_inc(x_182);
lean_dec(x_42);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_181);
x_184 = lean_ctor_get(x_4, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_4, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_4, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_4, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_4, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_4, 5);
lean_inc(x_189);
x_190 = lean_ctor_get(x_4, 6);
lean_inc(x_190);
x_191 = lean_ctor_get(x_4, 7);
lean_inc(x_191);
x_192 = lean_ctor_get(x_4, 8);
lean_inc(x_192);
x_193 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_194 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_195 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_196 = lean_ctor_get(x_4, 9);
lean_inc(x_196);
x_197 = l_Lean_Elab_replaceRef(x_36, x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_198, 0, x_184);
lean_ctor_set(x_198, 1, x_185);
lean_ctor_set(x_198, 2, x_186);
lean_ctor_set(x_198, 3, x_187);
lean_ctor_set(x_198, 4, x_188);
lean_ctor_set(x_198, 5, x_189);
lean_ctor_set(x_198, 6, x_190);
lean_ctor_set(x_198, 7, x_191);
lean_ctor_set(x_198, 8, x_192);
lean_ctor_set(x_198, 9, x_197);
lean_ctor_set_uint8(x_198, sizeof(void*)*10, x_193);
lean_ctor_set_uint8(x_198, sizeof(void*)*10 + 1, x_194);
lean_ctor_set_uint8(x_198, sizeof(void*)*10 + 2, x_195);
x_199 = 0;
x_200 = lean_box(0);
x_201 = l_Lean_Elab_Term_mkFreshExprMVar(x_183, x_199, x_200, x_198, x_43);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_203);
lean_inc(x_204);
x_205 = l_Lean_mkApp(x_30, x_204);
x_206 = lean_expr_instantiate1(x_182, x_204);
lean_dec(x_182);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_8, 3, x_207);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_206);
lean_ctor_set(x_2, 0, x_205);
lean_ctor_set(x_201, 0, x_2);
x_10 = x_201;
goto block_18;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_201, 0);
x_209 = lean_ctor_get(x_201, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_201);
x_210 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_208);
lean_inc(x_210);
x_211 = l_Lean_mkApp(x_30, x_210);
x_212 = lean_expr_instantiate1(x_182, x_210);
lean_dec(x_182);
x_213 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_8, 3, x_213);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_212);
lean_ctor_set(x_2, 0, x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_2);
lean_ctor_set(x_214, 1, x_209);
x_10 = x_214;
goto block_18;
}
}
}
}
else
{
lean_object* x_215; 
lean_free_object(x_8);
lean_dec(x_37);
lean_free_object(x_24);
lean_dec(x_35);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_215 = lean_box(0);
x_44 = x_215;
goto block_65;
}
block_65:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_44);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = l_Lean_indentExpr(x_45);
x_47 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_ctor_get(x_4, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 7);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 8);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_59 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_60 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_61 = lean_ctor_get(x_4, 9);
lean_inc(x_61);
x_62 = l_Lean_Elab_replaceRef(x_36, x_61);
lean_dec(x_61);
lean_dec(x_36);
x_63 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_63, 0, x_49);
lean_ctor_set(x_63, 1, x_50);
lean_ctor_set(x_63, 2, x_51);
lean_ctor_set(x_63, 3, x_52);
lean_ctor_set(x_63, 4, x_53);
lean_ctor_set(x_63, 5, x_54);
lean_ctor_set(x_63, 6, x_55);
lean_ctor_set(x_63, 7, x_56);
lean_ctor_set(x_63, 8, x_57);
lean_ctor_set(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*10, x_58);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 1, x_59);
lean_ctor_set_uint8(x_63, sizeof(void*)*10 + 2, x_60);
lean_inc(x_1);
x_64 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_40, x_1, x_48, x_63, x_43);
x_10 = x_64;
goto block_18;
}
}
else
{
uint8_t x_216; 
lean_dec(x_40);
lean_free_object(x_8);
lean_dec(x_37);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_216 = !lean_is_exclusive(x_41);
if (x_216 == 0)
{
x_10 = x_41;
goto block_18;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_41, 0);
x_218 = lean_ctor_get(x_41, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_41);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_10 = x_219;
goto block_18;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_24, 0);
x_221 = lean_ctor_get(x_24, 1);
x_222 = lean_ctor_get(x_8, 0);
x_223 = lean_ctor_get(x_8, 2);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_8);
x_224 = lean_ctor_get(x_27, 1);
lean_inc(x_224);
lean_dec(x_27);
lean_inc(x_4);
x_225 = l_Lean_Elab_Term_whnfForall(x_220, x_4, x_5);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
if (lean_obj_tag(x_226) == 7)
{
lean_dec(x_224);
switch (lean_obj_tag(x_223)) {
case 0:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_226, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_226, 2);
lean_inc(x_251);
lean_dec(x_226);
x_252 = lean_ctor_get(x_223, 0);
lean_inc(x_252);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_250);
x_254 = 1;
lean_inc(x_4);
lean_inc(x_253);
lean_inc(x_252);
x_255 = l_Lean_Elab_Term_elabTerm(x_252, x_253, x_254, x_4, x_227);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_ctor_get(x_4, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_4, 1);
lean_inc(x_259);
x_260 = lean_ctor_get(x_4, 2);
lean_inc(x_260);
x_261 = lean_ctor_get(x_4, 3);
lean_inc(x_261);
x_262 = lean_ctor_get(x_4, 4);
lean_inc(x_262);
x_263 = lean_ctor_get(x_4, 5);
lean_inc(x_263);
x_264 = lean_ctor_get(x_4, 6);
lean_inc(x_264);
x_265 = lean_ctor_get(x_4, 7);
lean_inc(x_265);
x_266 = lean_ctor_get(x_4, 8);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_268 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_269 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_270 = lean_ctor_get(x_4, 9);
lean_inc(x_270);
x_271 = l_Lean_Elab_replaceRef(x_252, x_270);
lean_dec(x_270);
lean_dec(x_252);
x_272 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_272, 0, x_258);
lean_ctor_set(x_272, 1, x_259);
lean_ctor_set(x_272, 2, x_260);
lean_ctor_set(x_272, 3, x_261);
lean_ctor_set(x_272, 4, x_262);
lean_ctor_set(x_272, 5, x_263);
lean_ctor_set(x_272, 6, x_264);
lean_ctor_set(x_272, 7, x_265);
lean_ctor_set(x_272, 8, x_266);
lean_ctor_set(x_272, 9, x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*10, x_267);
lean_ctor_set_uint8(x_272, sizeof(void*)*10 + 1, x_268);
lean_ctor_set_uint8(x_272, sizeof(void*)*10 + 2, x_269);
x_273 = l_Lean_Elab_Term_ensureHasType(x_253, x_256, x_272, x_257);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_276 = x_273;
} else {
 lean_dec_ref(x_273);
 x_276 = lean_box(0);
}
lean_inc(x_274);
x_277 = l_Lean_mkApp(x_30, x_274);
x_278 = lean_expr_instantiate1(x_251, x_274);
lean_dec(x_251);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_274);
x_280 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_280, 0, x_222);
lean_ctor_set(x_280, 1, x_25);
lean_ctor_set(x_280, 2, x_223);
lean_ctor_set(x_280, 3, x_279);
lean_ctor_set(x_3, 1, x_221);
lean_ctor_set(x_3, 0, x_280);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_278);
lean_ctor_set(x_2, 0, x_277);
if (lean_is_scalar(x_276)) {
 x_281 = lean_alloc_ctor(0, 2, 0);
} else {
 x_281 = x_276;
}
lean_ctor_set(x_281, 0, x_2);
lean_ctor_set(x_281, 1, x_275);
x_10 = x_281;
goto block_18;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_251);
lean_dec(x_223);
lean_dec(x_222);
lean_free_object(x_24);
lean_dec(x_221);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_282 = lean_ctor_get(x_273, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_273, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_284 = x_273;
} else {
 lean_dec_ref(x_273);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
x_10 = x_285;
goto block_18;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_251);
lean_dec(x_223);
lean_dec(x_222);
lean_free_object(x_24);
lean_dec(x_221);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_286 = lean_ctor_get(x_255, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_255, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_288 = x_255;
} else {
 lean_dec_ref(x_255);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
x_10 = x_289;
goto block_18;
}
}
case 1:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_free_object(x_2);
x_290 = lean_ctor_get(x_226, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_226, 2);
lean_inc(x_291);
lean_dec(x_226);
x_292 = lean_ctor_get(x_223, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 x_293 = x_223;
} else {
 lean_dec_ref(x_223);
 x_293 = lean_box(0);
}
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_290);
lean_inc(x_4);
lean_inc(x_294);
x_295 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_292, x_294, x_4, x_227);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_296, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_300 = x_296;
} else {
 lean_dec_ref(x_296);
 x_300 = lean_box(0);
}
lean_inc(x_4);
x_301 = l_Lean_Elab_Term_ensureHasType(x_294, x_298, x_4, x_297);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_304 = x_301;
} else {
 lean_dec_ref(x_301);
 x_304 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_305 = lean_alloc_ctor(1, 1, 0);
} else {
 x_305 = x_293;
}
lean_ctor_set(x_305, 0, x_299);
lean_inc(x_302);
x_306 = l_Lean_mkApp(x_30, x_302);
x_307 = lean_expr_instantiate1(x_291, x_302);
lean_dec(x_291);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_302);
x_309 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_309, 0, x_222);
lean_ctor_set(x_309, 1, x_25);
lean_ctor_set(x_309, 2, x_305);
lean_ctor_set(x_309, 3, x_308);
lean_ctor_set(x_3, 1, x_221);
lean_ctor_set(x_3, 0, x_309);
if (lean_is_scalar(x_300)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_300;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_3);
lean_ctor_set(x_24, 1, x_310);
lean_ctor_set(x_24, 0, x_306);
if (lean_is_scalar(x_304)) {
 x_311 = lean_alloc_ctor(0, 2, 0);
} else {
 x_311 = x_304;
}
lean_ctor_set(x_311, 0, x_24);
lean_ctor_set(x_311, 1, x_303);
x_10 = x_311;
goto block_18;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_222);
lean_free_object(x_24);
lean_dec(x_221);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_312 = lean_ctor_get(x_301, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_301, 1);
lean_inc(x_313);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_314 = x_301;
} else {
 lean_dec_ref(x_301);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(1, 2, 0);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_313);
x_10 = x_315;
goto block_18;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_294);
lean_dec(x_293);
lean_dec(x_291);
lean_dec(x_222);
lean_free_object(x_24);
lean_dec(x_221);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_316 = lean_ctor_get(x_295, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_295, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_318 = x_295;
} else {
 lean_dec_ref(x_295);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
x_10 = x_319;
goto block_18;
}
}
default: 
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_320 = lean_ctor_get(x_226, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_226, 2);
lean_inc(x_321);
lean_dec(x_226);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_320);
x_323 = lean_ctor_get(x_4, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_4, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_4, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_4, 3);
lean_inc(x_326);
x_327 = lean_ctor_get(x_4, 4);
lean_inc(x_327);
x_328 = lean_ctor_get(x_4, 5);
lean_inc(x_328);
x_329 = lean_ctor_get(x_4, 6);
lean_inc(x_329);
x_330 = lean_ctor_get(x_4, 7);
lean_inc(x_330);
x_331 = lean_ctor_get(x_4, 8);
lean_inc(x_331);
x_332 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_333 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_334 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_335 = lean_ctor_get(x_4, 9);
lean_inc(x_335);
x_336 = l_Lean_Elab_replaceRef(x_222, x_335);
lean_dec(x_335);
x_337 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_337, 0, x_323);
lean_ctor_set(x_337, 1, x_324);
lean_ctor_set(x_337, 2, x_325);
lean_ctor_set(x_337, 3, x_326);
lean_ctor_set(x_337, 4, x_327);
lean_ctor_set(x_337, 5, x_328);
lean_ctor_set(x_337, 6, x_329);
lean_ctor_set(x_337, 7, x_330);
lean_ctor_set(x_337, 8, x_331);
lean_ctor_set(x_337, 9, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*10, x_332);
lean_ctor_set_uint8(x_337, sizeof(void*)*10 + 1, x_333);
lean_ctor_set_uint8(x_337, sizeof(void*)*10 + 2, x_334);
x_338 = 0;
x_339 = lean_box(0);
x_340 = l_Lean_Elab_Term_mkFreshExprMVar(x_322, x_338, x_339, x_337, x_227);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 x_343 = x_340;
} else {
 lean_dec_ref(x_340);
 x_343 = lean_box(0);
}
x_344 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_341);
lean_inc(x_344);
x_345 = l_Lean_mkApp(x_30, x_344);
x_346 = lean_expr_instantiate1(x_321, x_344);
lean_dec(x_321);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_344);
x_348 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_348, 0, x_222);
lean_ctor_set(x_348, 1, x_25);
lean_ctor_set(x_348, 2, x_223);
lean_ctor_set(x_348, 3, x_347);
lean_ctor_set(x_3, 1, x_221);
lean_ctor_set(x_3, 0, x_348);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_346);
lean_ctor_set(x_2, 0, x_345);
if (lean_is_scalar(x_343)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_343;
}
lean_ctor_set(x_349, 0, x_2);
lean_ctor_set(x_349, 1, x_342);
x_10 = x_349;
goto block_18;
}
}
}
else
{
lean_object* x_350; 
lean_dec(x_223);
lean_free_object(x_24);
lean_dec(x_221);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_350 = lean_box(0);
x_228 = x_350;
goto block_249;
}
block_249:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_228);
x_229 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_229, 0, x_226);
x_230 = l_Lean_indentExpr(x_229);
x_231 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_232 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
x_233 = lean_ctor_get(x_4, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_4, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_4, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_4, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_4, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_4, 5);
lean_inc(x_238);
x_239 = lean_ctor_get(x_4, 6);
lean_inc(x_239);
x_240 = lean_ctor_get(x_4, 7);
lean_inc(x_240);
x_241 = lean_ctor_get(x_4, 8);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_243 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_244 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_245 = lean_ctor_get(x_4, 9);
lean_inc(x_245);
x_246 = l_Lean_Elab_replaceRef(x_222, x_245);
lean_dec(x_245);
lean_dec(x_222);
x_247 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_247, 0, x_233);
lean_ctor_set(x_247, 1, x_234);
lean_ctor_set(x_247, 2, x_235);
lean_ctor_set(x_247, 3, x_236);
lean_ctor_set(x_247, 4, x_237);
lean_ctor_set(x_247, 5, x_238);
lean_ctor_set(x_247, 6, x_239);
lean_ctor_set(x_247, 7, x_240);
lean_ctor_set(x_247, 8, x_241);
lean_ctor_set(x_247, 9, x_246);
lean_ctor_set_uint8(x_247, sizeof(void*)*10, x_242);
lean_ctor_set_uint8(x_247, sizeof(void*)*10 + 1, x_243);
lean_ctor_set_uint8(x_247, sizeof(void*)*10 + 2, x_244);
lean_inc(x_1);
x_248 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_224, x_1, x_232, x_247, x_227);
x_10 = x_248;
goto block_18;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_free_object(x_24);
lean_dec(x_221);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_351 = lean_ctor_get(x_225, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_225, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_353 = x_225;
} else {
 lean_dec_ref(x_225);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
x_10 = x_354;
goto block_18;
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_355 = lean_ctor_get(x_24, 0);
x_356 = lean_ctor_get(x_24, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_24);
x_357 = lean_ctor_get(x_8, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_8, 2);
lean_inc(x_358);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_359 = x_8;
} else {
 lean_dec_ref(x_8);
 x_359 = lean_box(0);
}
x_360 = lean_ctor_get(x_27, 1);
lean_inc(x_360);
lean_dec(x_27);
lean_inc(x_4);
x_361 = l_Lean_Elab_Term_whnfForall(x_355, x_4, x_5);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
if (lean_obj_tag(x_362) == 7)
{
lean_dec(x_360);
switch (lean_obj_tag(x_358)) {
case 0:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; uint8_t x_390; lean_object* x_391; 
x_386 = lean_ctor_get(x_362, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_362, 2);
lean_inc(x_387);
lean_dec(x_362);
x_388 = lean_ctor_get(x_358, 0);
lean_inc(x_388);
x_389 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_389, 0, x_386);
x_390 = 1;
lean_inc(x_4);
lean_inc(x_389);
lean_inc(x_388);
x_391 = l_Lean_Elab_Term_elabTerm(x_388, x_389, x_390, x_4, x_363);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = lean_ctor_get(x_4, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_4, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_4, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_4, 3);
lean_inc(x_397);
x_398 = lean_ctor_get(x_4, 4);
lean_inc(x_398);
x_399 = lean_ctor_get(x_4, 5);
lean_inc(x_399);
x_400 = lean_ctor_get(x_4, 6);
lean_inc(x_400);
x_401 = lean_ctor_get(x_4, 7);
lean_inc(x_401);
x_402 = lean_ctor_get(x_4, 8);
lean_inc(x_402);
x_403 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_404 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_405 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_406 = lean_ctor_get(x_4, 9);
lean_inc(x_406);
x_407 = l_Lean_Elab_replaceRef(x_388, x_406);
lean_dec(x_406);
lean_dec(x_388);
x_408 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_408, 0, x_394);
lean_ctor_set(x_408, 1, x_395);
lean_ctor_set(x_408, 2, x_396);
lean_ctor_set(x_408, 3, x_397);
lean_ctor_set(x_408, 4, x_398);
lean_ctor_set(x_408, 5, x_399);
lean_ctor_set(x_408, 6, x_400);
lean_ctor_set(x_408, 7, x_401);
lean_ctor_set(x_408, 8, x_402);
lean_ctor_set(x_408, 9, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*10, x_403);
lean_ctor_set_uint8(x_408, sizeof(void*)*10 + 1, x_404);
lean_ctor_set_uint8(x_408, sizeof(void*)*10 + 2, x_405);
x_409 = l_Lean_Elab_Term_ensureHasType(x_389, x_392, x_408, x_393);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
lean_inc(x_410);
x_413 = l_Lean_mkApp(x_30, x_410);
x_414 = lean_expr_instantiate1(x_387, x_410);
lean_dec(x_387);
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_410);
if (lean_is_scalar(x_359)) {
 x_416 = lean_alloc_ctor(0, 4, 0);
} else {
 x_416 = x_359;
}
lean_ctor_set(x_416, 0, x_357);
lean_ctor_set(x_416, 1, x_25);
lean_ctor_set(x_416, 2, x_358);
lean_ctor_set(x_416, 3, x_415);
lean_ctor_set(x_3, 1, x_356);
lean_ctor_set(x_3, 0, x_416);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_3);
lean_ctor_set(x_2, 1, x_417);
lean_ctor_set(x_2, 0, x_413);
if (lean_is_scalar(x_412)) {
 x_418 = lean_alloc_ctor(0, 2, 0);
} else {
 x_418 = x_412;
}
lean_ctor_set(x_418, 0, x_2);
lean_ctor_set(x_418, 1, x_411);
x_10 = x_418;
goto block_18;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_387);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_419 = lean_ctor_get(x_409, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_409, 1);
lean_inc(x_420);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_421 = x_409;
} else {
 lean_dec_ref(x_409);
 x_421 = lean_box(0);
}
if (lean_is_scalar(x_421)) {
 x_422 = lean_alloc_ctor(1, 2, 0);
} else {
 x_422 = x_421;
}
lean_ctor_set(x_422, 0, x_419);
lean_ctor_set(x_422, 1, x_420);
x_10 = x_422;
goto block_18;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_423 = lean_ctor_get(x_391, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_391, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_425 = x_391;
} else {
 lean_dec_ref(x_391);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
x_10 = x_426;
goto block_18;
}
}
case 1:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_free_object(x_2);
x_427 = lean_ctor_get(x_362, 1);
lean_inc(x_427);
x_428 = lean_ctor_get(x_362, 2);
lean_inc(x_428);
lean_dec(x_362);
x_429 = lean_ctor_get(x_358, 0);
lean_inc(x_429);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_430 = x_358;
} else {
 lean_dec_ref(x_358);
 x_430 = lean_box(0);
}
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_427);
lean_inc(x_4);
lean_inc(x_431);
x_432 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_429, x_431, x_4, x_363);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_433, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_437 = x_433;
} else {
 lean_dec_ref(x_433);
 x_437 = lean_box(0);
}
lean_inc(x_4);
x_438 = l_Lean_Elab_Term_ensureHasType(x_431, x_435, x_4, x_434);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_438, 1);
lean_inc(x_440);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_441 = x_438;
} else {
 lean_dec_ref(x_438);
 x_441 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_430;
}
lean_ctor_set(x_442, 0, x_436);
lean_inc(x_439);
x_443 = l_Lean_mkApp(x_30, x_439);
x_444 = lean_expr_instantiate1(x_428, x_439);
lean_dec(x_428);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_439);
if (lean_is_scalar(x_359)) {
 x_446 = lean_alloc_ctor(0, 4, 0);
} else {
 x_446 = x_359;
}
lean_ctor_set(x_446, 0, x_357);
lean_ctor_set(x_446, 1, x_25);
lean_ctor_set(x_446, 2, x_442);
lean_ctor_set(x_446, 3, x_445);
lean_ctor_set(x_3, 1, x_356);
lean_ctor_set(x_3, 0, x_446);
if (lean_is_scalar(x_437)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_437;
}
lean_ctor_set(x_447, 0, x_444);
lean_ctor_set(x_447, 1, x_3);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_443);
lean_ctor_set(x_448, 1, x_447);
if (lean_is_scalar(x_441)) {
 x_449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_449 = x_441;
}
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_440);
x_10 = x_449;
goto block_18;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_359);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_450 = lean_ctor_get(x_438, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_438, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_452 = x_438;
} else {
 lean_dec_ref(x_438);
 x_452 = lean_box(0);
}
if (lean_is_scalar(x_452)) {
 x_453 = lean_alloc_ctor(1, 2, 0);
} else {
 x_453 = x_452;
}
lean_ctor_set(x_453, 0, x_450);
lean_ctor_set(x_453, 1, x_451);
x_10 = x_453;
goto block_18;
}
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_359);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_454 = lean_ctor_get(x_432, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_432, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_456 = x_432;
} else {
 lean_dec_ref(x_432);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_454);
lean_ctor_set(x_457, 1, x_455);
x_10 = x_457;
goto block_18;
}
}
default: 
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_458 = lean_ctor_get(x_362, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_362, 2);
lean_inc(x_459);
lean_dec(x_362);
x_460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_460, 0, x_458);
x_461 = lean_ctor_get(x_4, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_4, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_4, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_4, 3);
lean_inc(x_464);
x_465 = lean_ctor_get(x_4, 4);
lean_inc(x_465);
x_466 = lean_ctor_get(x_4, 5);
lean_inc(x_466);
x_467 = lean_ctor_get(x_4, 6);
lean_inc(x_467);
x_468 = lean_ctor_get(x_4, 7);
lean_inc(x_468);
x_469 = lean_ctor_get(x_4, 8);
lean_inc(x_469);
x_470 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_471 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_472 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_473 = lean_ctor_get(x_4, 9);
lean_inc(x_473);
x_474 = l_Lean_Elab_replaceRef(x_357, x_473);
lean_dec(x_473);
x_475 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_475, 0, x_461);
lean_ctor_set(x_475, 1, x_462);
lean_ctor_set(x_475, 2, x_463);
lean_ctor_set(x_475, 3, x_464);
lean_ctor_set(x_475, 4, x_465);
lean_ctor_set(x_475, 5, x_466);
lean_ctor_set(x_475, 6, x_467);
lean_ctor_set(x_475, 7, x_468);
lean_ctor_set(x_475, 8, x_469);
lean_ctor_set(x_475, 9, x_474);
lean_ctor_set_uint8(x_475, sizeof(void*)*10, x_470);
lean_ctor_set_uint8(x_475, sizeof(void*)*10 + 1, x_471);
lean_ctor_set_uint8(x_475, sizeof(void*)*10 + 2, x_472);
x_476 = 0;
x_477 = lean_box(0);
x_478 = l_Lean_Elab_Term_mkFreshExprMVar(x_460, x_476, x_477, x_475, x_363);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
x_482 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_479);
lean_inc(x_482);
x_483 = l_Lean_mkApp(x_30, x_482);
x_484 = lean_expr_instantiate1(x_459, x_482);
lean_dec(x_459);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_482);
if (lean_is_scalar(x_359)) {
 x_486 = lean_alloc_ctor(0, 4, 0);
} else {
 x_486 = x_359;
}
lean_ctor_set(x_486, 0, x_357);
lean_ctor_set(x_486, 1, x_25);
lean_ctor_set(x_486, 2, x_358);
lean_ctor_set(x_486, 3, x_485);
lean_ctor_set(x_3, 1, x_356);
lean_ctor_set(x_3, 0, x_486);
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_3);
lean_ctor_set(x_2, 1, x_487);
lean_ctor_set(x_2, 0, x_483);
if (lean_is_scalar(x_481)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_481;
}
lean_ctor_set(x_488, 0, x_2);
lean_ctor_set(x_488, 1, x_480);
x_10 = x_488;
goto block_18;
}
}
}
else
{
lean_object* x_489; 
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_356);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_489 = lean_box(0);
x_364 = x_489;
goto block_385;
}
block_385:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; uint8_t x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_364);
x_365 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_365, 0, x_362);
x_366 = l_Lean_indentExpr(x_365);
x_367 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_368 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_368, 0, x_367);
lean_ctor_set(x_368, 1, x_366);
x_369 = lean_ctor_get(x_4, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_4, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_4, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_4, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_4, 4);
lean_inc(x_373);
x_374 = lean_ctor_get(x_4, 5);
lean_inc(x_374);
x_375 = lean_ctor_get(x_4, 6);
lean_inc(x_375);
x_376 = lean_ctor_get(x_4, 7);
lean_inc(x_376);
x_377 = lean_ctor_get(x_4, 8);
lean_inc(x_377);
x_378 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_379 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_380 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_381 = lean_ctor_get(x_4, 9);
lean_inc(x_381);
x_382 = l_Lean_Elab_replaceRef(x_357, x_381);
lean_dec(x_381);
lean_dec(x_357);
x_383 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_383, 0, x_369);
lean_ctor_set(x_383, 1, x_370);
lean_ctor_set(x_383, 2, x_371);
lean_ctor_set(x_383, 3, x_372);
lean_ctor_set(x_383, 4, x_373);
lean_ctor_set(x_383, 5, x_374);
lean_ctor_set(x_383, 6, x_375);
lean_ctor_set(x_383, 7, x_376);
lean_ctor_set(x_383, 8, x_377);
lean_ctor_set(x_383, 9, x_382);
lean_ctor_set_uint8(x_383, sizeof(void*)*10, x_378);
lean_ctor_set_uint8(x_383, sizeof(void*)*10 + 1, x_379);
lean_ctor_set_uint8(x_383, sizeof(void*)*10 + 2, x_380);
lean_inc(x_1);
x_384 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_360, x_1, x_368, x_383, x_363);
x_10 = x_384;
goto block_18;
}
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_490 = lean_ctor_get(x_361, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_361, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_492 = x_361;
} else {
 lean_dec_ref(x_361);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_491);
x_10 = x_493;
goto block_18;
}
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_494 = lean_ctor_get(x_2, 0);
lean_inc(x_494);
lean_dec(x_2);
x_495 = lean_ctor_get(x_24, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_24, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_497 = x_24;
} else {
 lean_dec_ref(x_24);
 x_497 = lean_box(0);
}
x_498 = lean_ctor_get(x_8, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_8, 2);
lean_inc(x_499);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_500 = x_8;
} else {
 lean_dec_ref(x_8);
 x_500 = lean_box(0);
}
x_501 = lean_ctor_get(x_27, 1);
lean_inc(x_501);
lean_dec(x_27);
lean_inc(x_4);
x_502 = l_Lean_Elab_Term_whnfForall(x_495, x_4, x_5);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
if (lean_obj_tag(x_503) == 7)
{
lean_dec(x_501);
switch (lean_obj_tag(x_499)) {
case 0:
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_531; lean_object* x_532; 
x_527 = lean_ctor_get(x_503, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_503, 2);
lean_inc(x_528);
lean_dec(x_503);
x_529 = lean_ctor_get(x_499, 0);
lean_inc(x_529);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_527);
x_531 = 1;
lean_inc(x_4);
lean_inc(x_530);
lean_inc(x_529);
x_532 = l_Lean_Elab_Term_elabTerm(x_529, x_530, x_531, x_4, x_504);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; uint8_t x_545; uint8_t x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_ctor_get(x_4, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_4, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_4, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_4, 3);
lean_inc(x_538);
x_539 = lean_ctor_get(x_4, 4);
lean_inc(x_539);
x_540 = lean_ctor_get(x_4, 5);
lean_inc(x_540);
x_541 = lean_ctor_get(x_4, 6);
lean_inc(x_541);
x_542 = lean_ctor_get(x_4, 7);
lean_inc(x_542);
x_543 = lean_ctor_get(x_4, 8);
lean_inc(x_543);
x_544 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_545 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_546 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_547 = lean_ctor_get(x_4, 9);
lean_inc(x_547);
x_548 = l_Lean_Elab_replaceRef(x_529, x_547);
lean_dec(x_547);
lean_dec(x_529);
x_549 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_549, 0, x_535);
lean_ctor_set(x_549, 1, x_536);
lean_ctor_set(x_549, 2, x_537);
lean_ctor_set(x_549, 3, x_538);
lean_ctor_set(x_549, 4, x_539);
lean_ctor_set(x_549, 5, x_540);
lean_ctor_set(x_549, 6, x_541);
lean_ctor_set(x_549, 7, x_542);
lean_ctor_set(x_549, 8, x_543);
lean_ctor_set(x_549, 9, x_548);
lean_ctor_set_uint8(x_549, sizeof(void*)*10, x_544);
lean_ctor_set_uint8(x_549, sizeof(void*)*10 + 1, x_545);
lean_ctor_set_uint8(x_549, sizeof(void*)*10 + 2, x_546);
x_550 = l_Lean_Elab_Term_ensureHasType(x_530, x_533, x_549, x_534);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_553 = x_550;
} else {
 lean_dec_ref(x_550);
 x_553 = lean_box(0);
}
lean_inc(x_551);
x_554 = l_Lean_mkApp(x_494, x_551);
x_555 = lean_expr_instantiate1(x_528, x_551);
lean_dec(x_528);
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_551);
if (lean_is_scalar(x_500)) {
 x_557 = lean_alloc_ctor(0, 4, 0);
} else {
 x_557 = x_500;
}
lean_ctor_set(x_557, 0, x_498);
lean_ctor_set(x_557, 1, x_25);
lean_ctor_set(x_557, 2, x_499);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_3, 1, x_496);
lean_ctor_set(x_3, 0, x_557);
if (lean_is_scalar(x_497)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_497;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_3);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_554);
lean_ctor_set(x_559, 1, x_558);
if (lean_is_scalar(x_553)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_553;
}
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_552);
x_10 = x_560;
goto block_18;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_528);
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_561 = lean_ctor_get(x_550, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_550, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_563 = x_550;
} else {
 lean_dec_ref(x_550);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
x_10 = x_564;
goto block_18;
}
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_528);
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_565 = lean_ctor_get(x_532, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_532, 1);
lean_inc(x_566);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_567 = x_532;
} else {
 lean_dec_ref(x_532);
 x_567 = lean_box(0);
}
if (lean_is_scalar(x_567)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_567;
}
lean_ctor_set(x_568, 0, x_565);
lean_ctor_set(x_568, 1, x_566);
x_10 = x_568;
goto block_18;
}
}
case 1:
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_569 = lean_ctor_get(x_503, 1);
lean_inc(x_569);
x_570 = lean_ctor_get(x_503, 2);
lean_inc(x_570);
lean_dec(x_503);
x_571 = lean_ctor_get(x_499, 0);
lean_inc(x_571);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 x_572 = x_499;
} else {
 lean_dec_ref(x_499);
 x_572 = lean_box(0);
}
x_573 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_573, 0, x_569);
lean_inc(x_4);
lean_inc(x_573);
x_574 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_571, x_573, x_4, x_504);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_574, 1);
lean_inc(x_576);
lean_dec(x_574);
x_577 = lean_ctor_get(x_575, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_575, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_575)) {
 lean_ctor_release(x_575, 0);
 lean_ctor_release(x_575, 1);
 x_579 = x_575;
} else {
 lean_dec_ref(x_575);
 x_579 = lean_box(0);
}
lean_inc(x_4);
x_580 = l_Lean_Elab_Term_ensureHasType(x_573, x_577, x_4, x_576);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_583 = x_580;
} else {
 lean_dec_ref(x_580);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_572)) {
 x_584 = lean_alloc_ctor(1, 1, 0);
} else {
 x_584 = x_572;
}
lean_ctor_set(x_584, 0, x_578);
lean_inc(x_581);
x_585 = l_Lean_mkApp(x_494, x_581);
x_586 = lean_expr_instantiate1(x_570, x_581);
lean_dec(x_570);
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_581);
if (lean_is_scalar(x_500)) {
 x_588 = lean_alloc_ctor(0, 4, 0);
} else {
 x_588 = x_500;
}
lean_ctor_set(x_588, 0, x_498);
lean_ctor_set(x_588, 1, x_25);
lean_ctor_set(x_588, 2, x_584);
lean_ctor_set(x_588, 3, x_587);
lean_ctor_set(x_3, 1, x_496);
lean_ctor_set(x_3, 0, x_588);
if (lean_is_scalar(x_579)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_579;
}
lean_ctor_set(x_589, 0, x_586);
lean_ctor_set(x_589, 1, x_3);
if (lean_is_scalar(x_497)) {
 x_590 = lean_alloc_ctor(0, 2, 0);
} else {
 x_590 = x_497;
}
lean_ctor_set(x_590, 0, x_585);
lean_ctor_set(x_590, 1, x_589);
if (lean_is_scalar(x_583)) {
 x_591 = lean_alloc_ctor(0, 2, 0);
} else {
 x_591 = x_583;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_582);
x_10 = x_591;
goto block_18;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_579);
lean_dec(x_578);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_500);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_592 = lean_ctor_get(x_580, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_580, 1);
lean_inc(x_593);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_594 = x_580;
} else {
 lean_dec_ref(x_580);
 x_594 = lean_box(0);
}
if (lean_is_scalar(x_594)) {
 x_595 = lean_alloc_ctor(1, 2, 0);
} else {
 x_595 = x_594;
}
lean_ctor_set(x_595, 0, x_592);
lean_ctor_set(x_595, 1, x_593);
x_10 = x_595;
goto block_18;
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_570);
lean_dec(x_500);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_596 = lean_ctor_get(x_574, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_574, 1);
lean_inc(x_597);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_598 = x_574;
} else {
 lean_dec_ref(x_574);
 x_598 = lean_box(0);
}
if (lean_is_scalar(x_598)) {
 x_599 = lean_alloc_ctor(1, 2, 0);
} else {
 x_599 = x_598;
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_597);
x_10 = x_599;
goto block_18;
}
}
default: 
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; uint8_t x_612; uint8_t x_613; uint8_t x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_600 = lean_ctor_get(x_503, 1);
lean_inc(x_600);
x_601 = lean_ctor_get(x_503, 2);
lean_inc(x_601);
lean_dec(x_503);
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_600);
x_603 = lean_ctor_get(x_4, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_4, 1);
lean_inc(x_604);
x_605 = lean_ctor_get(x_4, 2);
lean_inc(x_605);
x_606 = lean_ctor_get(x_4, 3);
lean_inc(x_606);
x_607 = lean_ctor_get(x_4, 4);
lean_inc(x_607);
x_608 = lean_ctor_get(x_4, 5);
lean_inc(x_608);
x_609 = lean_ctor_get(x_4, 6);
lean_inc(x_609);
x_610 = lean_ctor_get(x_4, 7);
lean_inc(x_610);
x_611 = lean_ctor_get(x_4, 8);
lean_inc(x_611);
x_612 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_613 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_614 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_615 = lean_ctor_get(x_4, 9);
lean_inc(x_615);
x_616 = l_Lean_Elab_replaceRef(x_498, x_615);
lean_dec(x_615);
x_617 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_617, 0, x_603);
lean_ctor_set(x_617, 1, x_604);
lean_ctor_set(x_617, 2, x_605);
lean_ctor_set(x_617, 3, x_606);
lean_ctor_set(x_617, 4, x_607);
lean_ctor_set(x_617, 5, x_608);
lean_ctor_set(x_617, 6, x_609);
lean_ctor_set(x_617, 7, x_610);
lean_ctor_set(x_617, 8, x_611);
lean_ctor_set(x_617, 9, x_616);
lean_ctor_set_uint8(x_617, sizeof(void*)*10, x_612);
lean_ctor_set_uint8(x_617, sizeof(void*)*10 + 1, x_613);
lean_ctor_set_uint8(x_617, sizeof(void*)*10 + 2, x_614);
x_618 = 0;
x_619 = lean_box(0);
x_620 = l_Lean_Elab_Term_mkFreshExprMVar(x_602, x_618, x_619, x_617, x_504);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
x_624 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_621);
lean_inc(x_624);
x_625 = l_Lean_mkApp(x_494, x_624);
x_626 = lean_expr_instantiate1(x_601, x_624);
lean_dec(x_601);
x_627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_627, 0, x_624);
if (lean_is_scalar(x_500)) {
 x_628 = lean_alloc_ctor(0, 4, 0);
} else {
 x_628 = x_500;
}
lean_ctor_set(x_628, 0, x_498);
lean_ctor_set(x_628, 1, x_25);
lean_ctor_set(x_628, 2, x_499);
lean_ctor_set(x_628, 3, x_627);
lean_ctor_set(x_3, 1, x_496);
lean_ctor_set(x_3, 0, x_628);
if (lean_is_scalar(x_497)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_497;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_3);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_625);
lean_ctor_set(x_630, 1, x_629);
if (lean_is_scalar(x_623)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_623;
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_622);
x_10 = x_631;
goto block_18;
}
}
}
else
{
lean_object* x_632; 
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_632 = lean_box(0);
x_505 = x_632;
goto block_526;
}
block_526:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; uint8_t x_520; uint8_t x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
lean_dec(x_505);
x_506 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_506, 0, x_503);
x_507 = l_Lean_indentExpr(x_506);
x_508 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_509 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_507);
x_510 = lean_ctor_get(x_4, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_4, 1);
lean_inc(x_511);
x_512 = lean_ctor_get(x_4, 2);
lean_inc(x_512);
x_513 = lean_ctor_get(x_4, 3);
lean_inc(x_513);
x_514 = lean_ctor_get(x_4, 4);
lean_inc(x_514);
x_515 = lean_ctor_get(x_4, 5);
lean_inc(x_515);
x_516 = lean_ctor_get(x_4, 6);
lean_inc(x_516);
x_517 = lean_ctor_get(x_4, 7);
lean_inc(x_517);
x_518 = lean_ctor_get(x_4, 8);
lean_inc(x_518);
x_519 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_520 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_521 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_522 = lean_ctor_get(x_4, 9);
lean_inc(x_522);
x_523 = l_Lean_Elab_replaceRef(x_498, x_522);
lean_dec(x_522);
lean_dec(x_498);
x_524 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_524, 0, x_510);
lean_ctor_set(x_524, 1, x_511);
lean_ctor_set(x_524, 2, x_512);
lean_ctor_set(x_524, 3, x_513);
lean_ctor_set(x_524, 4, x_514);
lean_ctor_set(x_524, 5, x_515);
lean_ctor_set(x_524, 6, x_516);
lean_ctor_set(x_524, 7, x_517);
lean_ctor_set(x_524, 8, x_518);
lean_ctor_set(x_524, 9, x_523);
lean_ctor_set_uint8(x_524, sizeof(void*)*10, x_519);
lean_ctor_set_uint8(x_524, sizeof(void*)*10 + 1, x_520);
lean_ctor_set_uint8(x_524, sizeof(void*)*10 + 2, x_521);
lean_inc(x_1);
x_525 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_501, x_1, x_509, x_524, x_504);
x_10 = x_525;
goto block_18;
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_494);
lean_dec(x_25);
lean_free_object(x_3);
x_633 = lean_ctor_get(x_502, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_502, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_635 = x_502;
} else {
 lean_dec_ref(x_502);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
x_10 = x_636;
goto block_18;
}
}
}
else
{
lean_object* x_637; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_637 = lean_box(0);
x_19 = x_637;
goto block_23;
}
}
else
{
lean_object* x_638; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_638 = lean_box(0);
x_19 = x_638;
goto block_23;
}
}
block_18:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_9;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_19);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_4);
x_22 = l_Lean_Elab_Term_throwErrorAt___rarg(x_20, x_21, x_4, x_5);
lean_dec(x_20);
x_10 = x_22;
goto block_18;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_650; lean_object* x_655; lean_object* x_656; 
x_639 = lean_ctor_get(x_3, 0);
x_640 = lean_ctor_get(x_3, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_3);
x_655 = lean_ctor_get(x_2, 1);
lean_inc(x_655);
x_656 = lean_ctor_get(x_639, 1);
lean_inc(x_656);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; 
lean_dec(x_655);
lean_dec(x_2);
x_657 = lean_box(0);
x_650 = x_657;
goto block_654;
}
else
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_656, 0);
lean_inc(x_658);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; 
x_659 = lean_ctor_get(x_656, 1);
lean_inc(x_659);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_660 = lean_ctor_get(x_2, 0);
lean_inc(x_660);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_661 = x_2;
} else {
 lean_dec_ref(x_2);
 x_661 = lean_box(0);
}
x_662 = lean_ctor_get(x_655, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_655, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_664 = x_655;
} else {
 lean_dec_ref(x_655);
 x_664 = lean_box(0);
}
x_665 = lean_ctor_get(x_639, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_639, 2);
lean_inc(x_666);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 lean_ctor_release(x_639, 1);
 lean_ctor_release(x_639, 2);
 lean_ctor_release(x_639, 3);
 x_667 = x_639;
} else {
 lean_dec_ref(x_639);
 x_667 = lean_box(0);
}
x_668 = lean_ctor_get(x_658, 1);
lean_inc(x_668);
lean_dec(x_658);
lean_inc(x_4);
x_669 = l_Lean_Elab_Term_whnfForall(x_662, x_4, x_5);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
if (lean_obj_tag(x_670) == 7)
{
lean_dec(x_668);
switch (lean_obj_tag(x_666)) {
case 0:
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; lean_object* x_699; 
x_694 = lean_ctor_get(x_670, 1);
lean_inc(x_694);
x_695 = lean_ctor_get(x_670, 2);
lean_inc(x_695);
lean_dec(x_670);
x_696 = lean_ctor_get(x_666, 0);
lean_inc(x_696);
x_697 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_697, 0, x_694);
x_698 = 1;
lean_inc(x_4);
lean_inc(x_697);
lean_inc(x_696);
x_699 = l_Lean_Elab_Term_elabTerm(x_696, x_697, x_698, x_4, x_671);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; uint8_t x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_4, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_4, 1);
lean_inc(x_703);
x_704 = lean_ctor_get(x_4, 2);
lean_inc(x_704);
x_705 = lean_ctor_get(x_4, 3);
lean_inc(x_705);
x_706 = lean_ctor_get(x_4, 4);
lean_inc(x_706);
x_707 = lean_ctor_get(x_4, 5);
lean_inc(x_707);
x_708 = lean_ctor_get(x_4, 6);
lean_inc(x_708);
x_709 = lean_ctor_get(x_4, 7);
lean_inc(x_709);
x_710 = lean_ctor_get(x_4, 8);
lean_inc(x_710);
x_711 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_712 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_713 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_714 = lean_ctor_get(x_4, 9);
lean_inc(x_714);
x_715 = l_Lean_Elab_replaceRef(x_696, x_714);
lean_dec(x_714);
lean_dec(x_696);
x_716 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_716, 0, x_702);
lean_ctor_set(x_716, 1, x_703);
lean_ctor_set(x_716, 2, x_704);
lean_ctor_set(x_716, 3, x_705);
lean_ctor_set(x_716, 4, x_706);
lean_ctor_set(x_716, 5, x_707);
lean_ctor_set(x_716, 6, x_708);
lean_ctor_set(x_716, 7, x_709);
lean_ctor_set(x_716, 8, x_710);
lean_ctor_set(x_716, 9, x_715);
lean_ctor_set_uint8(x_716, sizeof(void*)*10, x_711);
lean_ctor_set_uint8(x_716, sizeof(void*)*10 + 1, x_712);
lean_ctor_set_uint8(x_716, sizeof(void*)*10 + 2, x_713);
x_717 = l_Lean_Elab_Term_ensureHasType(x_697, x_700, x_716, x_701);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_720 = x_717;
} else {
 lean_dec_ref(x_717);
 x_720 = lean_box(0);
}
lean_inc(x_718);
x_721 = l_Lean_mkApp(x_660, x_718);
x_722 = lean_expr_instantiate1(x_695, x_718);
lean_dec(x_695);
x_723 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_723, 0, x_718);
if (lean_is_scalar(x_667)) {
 x_724 = lean_alloc_ctor(0, 4, 0);
} else {
 x_724 = x_667;
}
lean_ctor_set(x_724, 0, x_665);
lean_ctor_set(x_724, 1, x_656);
lean_ctor_set(x_724, 2, x_666);
lean_ctor_set(x_724, 3, x_723);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_663);
if (lean_is_scalar(x_664)) {
 x_726 = lean_alloc_ctor(0, 2, 0);
} else {
 x_726 = x_664;
}
lean_ctor_set(x_726, 0, x_722);
lean_ctor_set(x_726, 1, x_725);
if (lean_is_scalar(x_661)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_661;
}
lean_ctor_set(x_727, 0, x_721);
lean_ctor_set(x_727, 1, x_726);
if (lean_is_scalar(x_720)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_720;
}
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_719);
x_641 = x_728;
goto block_649;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_695);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_656);
x_729 = lean_ctor_get(x_717, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_717, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_731 = x_717;
} else {
 lean_dec_ref(x_717);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
x_641 = x_732;
goto block_649;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_656);
x_733 = lean_ctor_get(x_699, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_699, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_735 = x_699;
} else {
 lean_dec_ref(x_699);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
x_641 = x_736;
goto block_649;
}
}
case 1:
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_661);
x_737 = lean_ctor_get(x_670, 1);
lean_inc(x_737);
x_738 = lean_ctor_get(x_670, 2);
lean_inc(x_738);
lean_dec(x_670);
x_739 = lean_ctor_get(x_666, 0);
lean_inc(x_739);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 x_740 = x_666;
} else {
 lean_dec_ref(x_666);
 x_740 = lean_box(0);
}
x_741 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_741, 0, x_737);
lean_inc(x_4);
lean_inc(x_741);
x_742 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_739, x_741, x_4, x_671);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_ctor_get(x_743, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_743)) {
 lean_ctor_release(x_743, 0);
 lean_ctor_release(x_743, 1);
 x_747 = x_743;
} else {
 lean_dec_ref(x_743);
 x_747 = lean_box(0);
}
lean_inc(x_4);
x_748 = l_Lean_Elab_Term_ensureHasType(x_741, x_745, x_4, x_744);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_752 = lean_alloc_ctor(1, 1, 0);
} else {
 x_752 = x_740;
}
lean_ctor_set(x_752, 0, x_746);
lean_inc(x_749);
x_753 = l_Lean_mkApp(x_660, x_749);
x_754 = lean_expr_instantiate1(x_738, x_749);
lean_dec(x_738);
x_755 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_755, 0, x_749);
if (lean_is_scalar(x_667)) {
 x_756 = lean_alloc_ctor(0, 4, 0);
} else {
 x_756 = x_667;
}
lean_ctor_set(x_756, 0, x_665);
lean_ctor_set(x_756, 1, x_656);
lean_ctor_set(x_756, 2, x_752);
lean_ctor_set(x_756, 3, x_755);
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_663);
if (lean_is_scalar(x_747)) {
 x_758 = lean_alloc_ctor(0, 2, 0);
} else {
 x_758 = x_747;
}
lean_ctor_set(x_758, 0, x_754);
lean_ctor_set(x_758, 1, x_757);
if (lean_is_scalar(x_664)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_664;
}
lean_ctor_set(x_759, 0, x_753);
lean_ctor_set(x_759, 1, x_758);
if (lean_is_scalar(x_751)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_751;
}
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_750);
x_641 = x_760;
goto block_649;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_667);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_660);
lean_dec(x_656);
x_761 = lean_ctor_get(x_748, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_748, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_763 = x_748;
} else {
 lean_dec_ref(x_748);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
x_641 = x_764;
goto block_649;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_738);
lean_dec(x_667);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_660);
lean_dec(x_656);
x_765 = lean_ctor_get(x_742, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_742, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_767 = x_742;
} else {
 lean_dec_ref(x_742);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
x_641 = x_768;
goto block_649;
}
}
default: 
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; uint8_t x_782; uint8_t x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; uint8_t x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_769 = lean_ctor_get(x_670, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_670, 2);
lean_inc(x_770);
lean_dec(x_670);
x_771 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_771, 0, x_769);
x_772 = lean_ctor_get(x_4, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_4, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_4, 2);
lean_inc(x_774);
x_775 = lean_ctor_get(x_4, 3);
lean_inc(x_775);
x_776 = lean_ctor_get(x_4, 4);
lean_inc(x_776);
x_777 = lean_ctor_get(x_4, 5);
lean_inc(x_777);
x_778 = lean_ctor_get(x_4, 6);
lean_inc(x_778);
x_779 = lean_ctor_get(x_4, 7);
lean_inc(x_779);
x_780 = lean_ctor_get(x_4, 8);
lean_inc(x_780);
x_781 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_782 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_783 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_784 = lean_ctor_get(x_4, 9);
lean_inc(x_784);
x_785 = l_Lean_Elab_replaceRef(x_665, x_784);
lean_dec(x_784);
x_786 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_786, 0, x_772);
lean_ctor_set(x_786, 1, x_773);
lean_ctor_set(x_786, 2, x_774);
lean_ctor_set(x_786, 3, x_775);
lean_ctor_set(x_786, 4, x_776);
lean_ctor_set(x_786, 5, x_777);
lean_ctor_set(x_786, 6, x_778);
lean_ctor_set(x_786, 7, x_779);
lean_ctor_set(x_786, 8, x_780);
lean_ctor_set(x_786, 9, x_785);
lean_ctor_set_uint8(x_786, sizeof(void*)*10, x_781);
lean_ctor_set_uint8(x_786, sizeof(void*)*10 + 1, x_782);
lean_ctor_set_uint8(x_786, sizeof(void*)*10 + 2, x_783);
x_787 = 0;
x_788 = lean_box(0);
x_789 = l_Lean_Elab_Term_mkFreshExprMVar(x_771, x_787, x_788, x_786, x_671);
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_792 = x_789;
} else {
 lean_dec_ref(x_789);
 x_792 = lean_box(0);
}
x_793 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_790);
lean_inc(x_793);
x_794 = l_Lean_mkApp(x_660, x_793);
x_795 = lean_expr_instantiate1(x_770, x_793);
lean_dec(x_770);
x_796 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_796, 0, x_793);
if (lean_is_scalar(x_667)) {
 x_797 = lean_alloc_ctor(0, 4, 0);
} else {
 x_797 = x_667;
}
lean_ctor_set(x_797, 0, x_665);
lean_ctor_set(x_797, 1, x_656);
lean_ctor_set(x_797, 2, x_666);
lean_ctor_set(x_797, 3, x_796);
x_798 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_663);
if (lean_is_scalar(x_664)) {
 x_799 = lean_alloc_ctor(0, 2, 0);
} else {
 x_799 = x_664;
}
lean_ctor_set(x_799, 0, x_795);
lean_ctor_set(x_799, 1, x_798);
if (lean_is_scalar(x_661)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_661;
}
lean_ctor_set(x_800, 0, x_794);
lean_ctor_set(x_800, 1, x_799);
if (lean_is_scalar(x_792)) {
 x_801 = lean_alloc_ctor(0, 2, 0);
} else {
 x_801 = x_792;
}
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_791);
x_641 = x_801;
goto block_649;
}
}
}
else
{
lean_object* x_802; 
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_656);
x_802 = lean_box(0);
x_672 = x_802;
goto block_693;
}
block_693:
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; uint8_t x_687; uint8_t x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
lean_dec(x_672);
x_673 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_673, 0, x_670);
x_674 = l_Lean_indentExpr(x_673);
x_675 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_676 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_676, 0, x_675);
lean_ctor_set(x_676, 1, x_674);
x_677 = lean_ctor_get(x_4, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_4, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_4, 2);
lean_inc(x_679);
x_680 = lean_ctor_get(x_4, 3);
lean_inc(x_680);
x_681 = lean_ctor_get(x_4, 4);
lean_inc(x_681);
x_682 = lean_ctor_get(x_4, 5);
lean_inc(x_682);
x_683 = lean_ctor_get(x_4, 6);
lean_inc(x_683);
x_684 = lean_ctor_get(x_4, 7);
lean_inc(x_684);
x_685 = lean_ctor_get(x_4, 8);
lean_inc(x_685);
x_686 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_687 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_688 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_689 = lean_ctor_get(x_4, 9);
lean_inc(x_689);
x_690 = l_Lean_Elab_replaceRef(x_665, x_689);
lean_dec(x_689);
lean_dec(x_665);
x_691 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_691, 0, x_677);
lean_ctor_set(x_691, 1, x_678);
lean_ctor_set(x_691, 2, x_679);
lean_ctor_set(x_691, 3, x_680);
lean_ctor_set(x_691, 4, x_681);
lean_ctor_set(x_691, 5, x_682);
lean_ctor_set(x_691, 6, x_683);
lean_ctor_set(x_691, 7, x_684);
lean_ctor_set(x_691, 8, x_685);
lean_ctor_set(x_691, 9, x_690);
lean_ctor_set_uint8(x_691, sizeof(void*)*10, x_686);
lean_ctor_set_uint8(x_691, sizeof(void*)*10 + 1, x_687);
lean_ctor_set_uint8(x_691, sizeof(void*)*10 + 2, x_688);
lean_inc(x_1);
x_692 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_668, x_1, x_676, x_691, x_671);
x_641 = x_692;
goto block_649;
}
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; 
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_661);
lean_dec(x_660);
lean_dec(x_656);
x_803 = lean_ctor_get(x_669, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_669, 1);
lean_inc(x_804);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_805 = x_669;
} else {
 lean_dec_ref(x_669);
 x_805 = lean_box(0);
}
if (lean_is_scalar(x_805)) {
 x_806 = lean_alloc_ctor(1, 2, 0);
} else {
 x_806 = x_805;
}
lean_ctor_set(x_806, 0, x_803);
lean_ctor_set(x_806, 1, x_804);
x_641 = x_806;
goto block_649;
}
}
else
{
lean_object* x_807; 
lean_dec(x_659);
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_2);
x_807 = lean_box(0);
x_650 = x_807;
goto block_654;
}
}
else
{
lean_object* x_808; 
lean_dec(x_658);
lean_dec(x_656);
lean_dec(x_655);
lean_dec(x_2);
x_808 = lean_box(0);
x_650 = x_808;
goto block_654;
}
}
block_649:
{
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_2 = x_642;
x_3 = x_640;
x_5 = x_643;
goto _start;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
lean_dec(x_640);
lean_dec(x_4);
lean_dec(x_1);
x_645 = lean_ctor_get(x_641, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_641, 1);
lean_inc(x_646);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_647 = x_641;
} else {
 lean_dec_ref(x_641);
 x_647 = lean_box(0);
}
if (lean_is_scalar(x_647)) {
 x_648 = lean_alloc_ctor(1, 2, 0);
} else {
 x_648 = x_647;
}
lean_ctor_set(x_648, 0, x_645);
lean_ctor_set(x_648, 1, x_646);
return x_648;
}
}
block_654:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_650);
x_651 = lean_ctor_get(x_639, 0);
lean_inc(x_651);
lean_dec(x_639);
x_652 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_4);
x_653 = l_Lean_Elab_Term_throwErrorAt___rarg(x_651, x_652, x_4, x_5);
lean_dec(x_651);
x_641 = x_653;
goto block_649;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_3, 9);
x_8 = l_Lean_Elab_replaceRef(x_5, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_ctor_set(x_3, 9, x_8);
x_9 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_12);
x_13 = l_Lean_getStructureCtor(x_10, x_12);
lean_inc(x_3);
x_14 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_13, x_2, x_3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_23 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_12, x_21, x_22, x_3, x_16);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = l_List_reverse___rarg(x_30);
x_33 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_32);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_28);
lean_ctor_set(x_23, 0, x_25);
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = l_List_reverse___rarg(x_34);
x_36 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_23, 0, x_37);
return x_23;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_dec(x_23);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_41 = x_25;
} else {
 lean_dec_ref(x_25);
 x_41 = lean_box(0);
}
x_42 = l_List_reverse___rarg(x_40);
x_43 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_39);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
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
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
return x_14;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_14);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_54 = lean_ctor_get(x_3, 0);
x_55 = lean_ctor_get(x_3, 1);
x_56 = lean_ctor_get(x_3, 2);
x_57 = lean_ctor_get(x_3, 3);
x_58 = lean_ctor_get(x_3, 4);
x_59 = lean_ctor_get(x_3, 5);
x_60 = lean_ctor_get(x_3, 6);
x_61 = lean_ctor_get(x_3, 7);
x_62 = lean_ctor_get(x_3, 8);
x_63 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_64 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_65 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_66 = lean_ctor_get(x_3, 9);
lean_inc(x_66);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_3);
x_67 = l_Lean_Elab_replaceRef(x_5, x_66);
lean_dec(x_66);
lean_dec(x_5);
x_68 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_68, 0, x_54);
lean_ctor_set(x_68, 1, x_55);
lean_ctor_set(x_68, 2, x_56);
lean_ctor_set(x_68, 3, x_57);
lean_ctor_set(x_68, 4, x_58);
lean_ctor_set(x_68, 5, x_59);
lean_ctor_set(x_68, 6, x_60);
lean_ctor_set(x_68, 7, x_61);
lean_ctor_set(x_68, 8, x_62);
lean_ctor_set(x_68, 9, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*10, x_63);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 1, x_64);
lean_ctor_set_uint8(x_68, sizeof(void*)*10 + 2, x_65);
x_69 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_72);
x_73 = l_Lean_getStructureCtor(x_70, x_72);
lean_inc(x_68);
x_74 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_73, x_2, x_68, x_71);
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
x_83 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_72, x_81, x_82, x_68, x_76);
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
lean_dec(x_68);
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
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_6, x_1);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
x_4 = lean_array_push(x_2, x_3);
x_5 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_6 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_2);
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
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_6);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
return x_2;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_23; 
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_24);
lean_dec(x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_23);
x_26 = lean_box(0);
x_3 = x_26;
goto block_22;
}
block_22:
{
lean_object* x_4; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = l_unreachable_x21___rarg(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_metavar_ctx_is_expr_assigned(x_1, x_12);
if (x_13 == 0)
{
lean_ctor_set(x_8, 0, x_2);
return x_8;
}
else
{
lean_object* x_14; 
lean_free_object(x_8);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
else
{
lean_object* x_15; 
lean_free_object(x_8);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_metavar_ctx_is_expr_assigned(x_1, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_2);
x_20 = lean_box(0);
return x_20;
}
}
else
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
return x_21;
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Elab_Term_StructInst_Struct_fields(x_2);
x_5 = l_List_findSome_x3f___main___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_1, x_2);
return x_3;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Name_inhabited;
x_4 = l_unreachable_x21___rarg(x_3);
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
x_8 = l_Lean_Name_inhabited;
x_9 = l_unreachable_x21___rarg(x_8);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Name_inhabited;
x_11 = l_unreachable_x21___rarg(x_10);
return x_11;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_unbox(x_2);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
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
x_5 = l_List_findSome_x3f___main___rarg(x_3, x_4);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_19 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_20 = (uint8_t)((x_18 << 24) >> 61);
x_21 = l_Lean_BinderInfo_isExplicit(x_20);
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_3, 9);
x_24 = l_Lean_Elab_replaceRef(x_19, x_23);
lean_dec(x_23);
lean_dec(x_19);
lean_ctor_set(x_3, 9, x_24);
if (x_21 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_16);
x_26 = 0;
x_27 = lean_box(0);
lean_inc(x_3);
x_28 = l_Lean_Elab_Term_mkFreshExprMVar(x_25, x_26, x_27, x_3, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_expr_instantiate1(x_17, x_29);
lean_dec(x_29);
lean_dec(x_17);
x_2 = x_31;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_15);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_3);
lean_inc(x_35);
x_36 = l_Lean_Elab_Term_inferType(x_35, x_3, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_3);
x_39 = l_Lean_Elab_Term_isDefEq(x_37, x_16, x_3, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; 
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_17);
x_42 = !lean_is_exclusive(x_39);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_39, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = lean_expr_instantiate1(x_17, x_35);
lean_dec(x_35);
lean_dec(x_17);
x_2 = x_49;
x_4 = x_48;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_17);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
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
lean_dec(x_35);
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_16);
x_55 = !lean_is_exclusive(x_36);
if (x_55 == 0)
{
return x_36;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_36, 0);
x_57 = lean_ctor_get(x_36, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_36);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get(x_3, 1);
x_61 = lean_ctor_get(x_3, 2);
x_62 = lean_ctor_get(x_3, 3);
x_63 = lean_ctor_get(x_3, 4);
x_64 = lean_ctor_get(x_3, 5);
x_65 = lean_ctor_get(x_3, 6);
x_66 = lean_ctor_get(x_3, 7);
x_67 = lean_ctor_get(x_3, 8);
x_68 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_69 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_70 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_71 = lean_ctor_get(x_3, 9);
lean_inc(x_71);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_3);
x_72 = l_Lean_Elab_replaceRef(x_19, x_71);
lean_dec(x_71);
lean_dec(x_19);
x_73 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_73, 0, x_59);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_61);
lean_ctor_set(x_73, 3, x_62);
lean_ctor_set(x_73, 4, x_63);
lean_ctor_set(x_73, 5, x_64);
lean_ctor_set(x_73, 6, x_65);
lean_ctor_set(x_73, 7, x_66);
lean_ctor_set(x_73, 8, x_67);
lean_ctor_set(x_73, 9, x_72);
lean_ctor_set_uint8(x_73, sizeof(void*)*10, x_68);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 1, x_69);
lean_ctor_set_uint8(x_73, sizeof(void*)*10 + 2, x_70);
if (x_21 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_16);
x_75 = 0;
x_76 = lean_box(0);
lean_inc(x_73);
x_77 = l_Lean_Elab_Term_mkFreshExprMVar(x_74, x_75, x_76, x_73, x_4);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_expr_instantiate1(x_17, x_78);
lean_dec(x_78);
lean_dec(x_17);
x_2 = x_80;
x_3 = x_73;
x_4 = x_79;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_15);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_73);
lean_dec(x_17);
lean_dec(x_16);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_4);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_73);
lean_inc(x_84);
x_85 = l_Lean_Elab_Term_inferType(x_84, x_73, x_4);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_73);
x_88 = l_Lean_Elab_Term_isDefEq(x_86, x_16, x_73, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_17);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
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
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_88, 1);
lean_inc(x_95);
lean_dec(x_88);
x_96 = lean_expr_instantiate1(x_17, x_84);
lean_dec(x_84);
lean_dec(x_17);
x_2 = x_96;
x_3 = x_73;
x_4 = x_95;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_17);
x_98 = lean_ctor_get(x_88, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_88, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_100 = x_88;
} else {
 lean_dec_ref(x_88);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_17);
lean_dec(x_16);
x_102 = lean_ctor_get(x_85, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_85, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_104 = x_85;
} else {
 lean_dec_ref(x_85);
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
}
}
else
{
lean_object* x_106; 
lean_dec(x_3);
x_106 = lean_box(0);
x_5 = x_106;
goto block_14;
}
block_14:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = l_Lean_Meta_mkId___closed__1;
x_7 = lean_unsigned_to_nat(2u);
x_8 = l_Lean_Expr_isAppOfArity___main(x_2, x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_6 = l_Lean_ConstantInfo_lparams(x_2);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_3, 9);
x_9 = l_Lean_Elab_replaceRef(x_5, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_ctor_set(x_3, 9, x_9);
lean_inc(x_3);
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_6, x_3, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_instantiate_value_lparams(x_2, x_11);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_13, x_3, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
x_18 = lean_ctor_get(x_3, 3);
x_19 = lean_ctor_get(x_3, 4);
x_20 = lean_ctor_get(x_3, 5);
x_21 = lean_ctor_get(x_3, 6);
x_22 = lean_ctor_get(x_3, 7);
x_23 = lean_ctor_get(x_3, 8);
x_24 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_25 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_27 = lean_ctor_get(x_3, 9);
lean_inc(x_27);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_28 = l_Lean_Elab_replaceRef(x_5, x_27);
lean_dec(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_16);
lean_ctor_set(x_29, 2, x_17);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_19);
lean_ctor_set(x_29, 5, x_20);
lean_ctor_set(x_29, 6, x_21);
lean_ctor_set(x_29, 7, x_22);
lean_ctor_set(x_29, 8, x_23);
lean_ctor_set(x_29, 9, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*10, x_24);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 1, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*10 + 2, x_26);
lean_inc(x_29);
x_30 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_6, x_29, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_instantiate_value_lparams(x_2, x_31);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_33, x_29, x_32);
return x_34;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isApp(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_8) == 4)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = l_Lean_Environment_getProjectionStructureName_x3f(x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_WHNF_unfoldDefinitionAux___at_Lean_Meta_unfoldDefinition_x3f___spec__1(x_2, x_3, x_4);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = x_3;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_3, x_2);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_fset(x_3, x_2, x_11);
x_13 = x_10;
lean_inc(x_4);
lean_inc(x_1);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
x_19 = x_15;
x_20 = lean_array_fset(x_12, x_2, x_19);
lean_dec(x_2);
x_2 = x_18;
x_3 = x_20;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_mkLambda(x_2, x_7, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_mkForall(x_2, x_7, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_metavar_ctx_get_expr_assignment(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_isMVar(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
x_2 = x_9;
goto _start;
}
}
}
case 5:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(x_1, x_2, x_3, x_4);
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
x_17 = l_Lean_Expr_getAppFn___main(x_13);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_1);
x_18 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_17, x_3, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Expr_isLambda(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_22);
x_24 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_23, x_26);
lean_dec(x_23);
x_28 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_25, x_27);
x_29 = x_28;
x_30 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1), 5, 3);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_22);
lean_closure_set(x_30, 2, x_29);
x_31 = x_30;
x_32 = lean_apply_2(x_31, x_3, x_20);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_34, x_34, x_22, x_19);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_36, x_36, x_22, x_19);
lean_dec(x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_19);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_44);
x_46 = lean_mk_empty_array_with_capacity(x_45);
lean_dec(x_45);
x_47 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_46);
x_48 = l_Lean_Expr_betaRev(x_19, x_47);
lean_dec(x_47);
lean_dec(x_19);
x_2 = x_48;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
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
lean_dec(x_13);
lean_dec(x_2);
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_ctor_get(x_15, 0);
lean_inc(x_55);
lean_dec(x_15);
x_2 = x_55;
x_4 = x_54;
goto _start;
}
}
else
{
uint8_t x_57; 
lean_dec(x_13);
lean_dec(x_3);
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
case 6:
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 5, 1);
lean_closure_set(x_61, 0, x_1);
x_62 = l_Lean_Meta_lambdaTelescope___rarg(x_2, x_61, x_3, x_4);
return x_62;
}
case 7:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2), 5, 1);
lean_closure_set(x_63, 0, x_1);
x_64 = l_Lean_Meta_forallTelescope___rarg(x_2, x_63, x_3, x_4);
return x_64;
}
case 8:
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 5, 1);
lean_closure_set(x_65, 0, x_1);
x_66 = l_Lean_Meta_lambdaTelescope___rarg(x_2, x_65, x_3, x_4);
return x_66;
}
case 10:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
x_68 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_67, x_3, x_4);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; 
x_72 = lean_expr_update_mdata(x_2, x_70);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
uint8_t x_73; 
lean_dec(x_71);
x_73 = l_Lean_Expr_isMVar(x_70);
if (x_73 == 0)
{
lean_dec(x_2);
return x_68;
}
else
{
lean_object* x_74; 
x_74 = lean_expr_update_mdata(x_2, x_70);
lean_ctor_set(x_68, 0, x_74);
return x_68;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_77 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_expr_update_mdata(x_2, x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
uint8_t x_80; 
lean_dec(x_77);
x_80 = l_Lean_Expr_isMVar(x_75);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_76);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_expr_update_mdata(x_2, x_75);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_2);
x_84 = !lean_is_exclusive(x_68);
if (x_84 == 0)
{
return x_68;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
case 11:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 2);
lean_inc(x_89);
lean_inc(x_3);
lean_inc(x_89);
x_90 = l_Lean_Meta_reduceProj_x3f(x_89, x_88, x_3, x_4);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_89, x_3, x_92);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_expr_update_proj(x_2, x_95);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_93, 0);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_93);
x_99 = lean_expr_update_proj(x_2, x_97);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_93);
if (x_101 == 0)
{
return x_93;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_93, 0);
x_103 = lean_ctor_get(x_93, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_93);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_89);
lean_dec(x_2);
x_105 = lean_ctor_get(x_90, 1);
lean_inc(x_105);
lean_dec(x_90);
x_106 = lean_ctor_get(x_91, 0);
lean_inc(x_106);
lean_dec(x_91);
x_2 = x_106;
x_4 = x_105;
goto _start;
}
}
else
{
uint8_t x_108; 
lean_dec(x_89);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_90);
if (x_108 == 0)
{
return x_90;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_90, 0);
x_110 = lean_ctor_get(x_90, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_90);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
default: 
{
lean_object* x_112; 
lean_dec(x_3);
lean_dec(x_1);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_4);
return x_112;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(size_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; size_t x_99; size_t x_100; lean_object* x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ptr_addr(x_2);
x_100 = x_1 == 0 ? 0 : x_99 % x_1;
x_101 = lean_array_uget(x_3, x_100);
x_102 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_103 = x_102 == x_99;
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
lean_inc(x_2);
x_104 = lean_array_uset(x_3, x_100, x_2);
x_105 = 0;
x_4 = x_105;
x_5 = x_104;
goto block_98;
}
else
{
uint8_t x_106; 
x_106 = 1;
x_4 = x_106;
x_5 = x_3;
goto block_98;
}
block_98:
{
if (x_4 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_6) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_7, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
if (lean_is_scalar(x_20)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_20;
}
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
}
case 6:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_23, x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_2 = x_24;
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_25, 0, x_33);
return x_25;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_34);
return x_38;
}
}
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 2);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_39, x_5);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_2 = x_40;
x_3 = x_43;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_40);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec(x_41);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_52 = x_42;
} else {
 lean_dec_ref(x_42);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
}
case 8:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_2, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_2, 3);
lean_inc(x_57);
lean_dec(x_2);
x_58 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_55, x_5);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_1, x_56, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_2 = x_57;
x_3 = x_63;
goto _start;
}
else
{
uint8_t x_65; 
lean_dec(x_57);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_61, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_61;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_61, 0, x_69);
return x_61;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_dec(x_61);
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_72 = x_62;
} else {
 lean_dec_ref(x_62);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_57);
lean_dec(x_56);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_58, 0);
lean_dec(x_76);
x_77 = !lean_is_exclusive(x_59);
if (x_77 == 0)
{
return x_58;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_59, 0);
lean_inc(x_78);
lean_dec(x_59);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_58, 0, x_79);
return x_58;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_dec(x_58);
x_81 = lean_ctor_get(x_59, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_82 = x_59;
} else {
 lean_dec_ref(x_59);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
}
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_2, 1);
lean_inc(x_85);
lean_dec(x_2);
x_2 = x_85;
x_3 = x_5;
goto _start;
}
case 11:
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
lean_dec(x_2);
x_2 = x_87;
x_3 = x_5;
goto _start;
}
default: 
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_2);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_5);
return x_90;
}
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_6, 0);
lean_dec(x_92);
lean_ctor_set(x_6, 0, x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_6);
lean_ctor_set(x_93, 1, x_5);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_6);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_2);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_5);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_2);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_5);
return x_97;
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_nat_dec_lt(x_3, x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_6, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_array_fget(x_1, x_6);
x_17 = l_Lean_Elab_Term_StructInst_Struct_structName(x_16);
lean_inc(x_4);
x_18 = l_Lean_Name_append___main(x_17, x_4);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
x_20 = l_Lean_Name_append___main(x_18, x_19);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_find(x_22, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_16);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_6, x_25);
lean_dec(x_6);
x_6 = x_26;
x_9 = x_23;
goto _start;
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = l_Lean_Elab_Term_getMCtx___rarg(x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_8);
x_32 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_16, x_28, x_8, x_31);
lean_dec(x_28);
lean_dec(x_16);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_6, x_35);
lean_dec(x_6);
x_37 = lean_nat_add(x_7, x_35);
lean_dec(x_7);
x_38 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_34);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_6 = x_36;
x_7 = x_37;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = !lean_is_exclusive(x_33);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_33, 0);
x_46 = lean_ctor_get(x_42, 4);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
x_48 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_42, 4, x_48);
lean_inc(x_2);
x_49 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_45, x_47, x_42);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_8);
x_52 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_51, x_46);
x_53 = 8192;
x_54 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_50);
x_55 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_53, x_50, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_57 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_52);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 2);
lean_inc(x_60);
lean_dec(x_58);
lean_ctor_set(x_33, 0, x_60);
lean_inc(x_8);
x_61 = l_Lean_Elab_Term_ensureHasType(x_33, x_50, x_8, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_Term_assignExprMVar(x_5, x_62, x_8, x_63);
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = 1;
x_68 = lean_box(x_67);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = 1;
x_71 = lean_box(x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_8);
lean_dec(x_5);
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
return x_61;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_ctor_get(x_61, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_61);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
lean_dec(x_50);
lean_free_object(x_33);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_6, x_77);
lean_dec(x_6);
x_79 = lean_nat_add(x_7, x_77);
lean_dec(x_7);
x_80 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_52);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_6 = x_78;
x_7 = x_79;
x_9 = x_81;
goto _start;
}
}
else
{
uint8_t x_83; 
lean_free_object(x_33);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_83 = !lean_is_exclusive(x_49);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_49, 0);
x_85 = lean_ctor_get(x_49, 1);
lean_inc(x_8);
x_86 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_84);
x_87 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_85, x_46);
lean_ctor_set(x_49, 1, x_87);
lean_ctor_set(x_49, 0, x_86);
return x_49;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_49, 0);
x_89 = lean_ctor_get(x_49, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_49);
lean_inc(x_8);
x_90 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_88);
x_91 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_89, x_46);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_93 = lean_ctor_get(x_33, 0);
x_94 = lean_ctor_get(x_42, 0);
x_95 = lean_ctor_get(x_42, 1);
x_96 = lean_ctor_get(x_42, 2);
x_97 = lean_ctor_get(x_42, 3);
x_98 = lean_ctor_get(x_42, 4);
x_99 = lean_ctor_get(x_42, 5);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_42);
x_100 = lean_ctor_get(x_8, 0);
lean_inc(x_100);
x_101 = l_Lean_TraceState_Inhabited___closed__1;
x_102 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_102, 0, x_94);
lean_ctor_set(x_102, 1, x_95);
lean_ctor_set(x_102, 2, x_96);
lean_ctor_set(x_102, 3, x_97);
lean_ctor_set(x_102, 4, x_101);
lean_ctor_set(x_102, 5, x_99);
lean_inc(x_2);
x_103 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_93, x_100, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; size_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_8);
x_106 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_105, x_98);
x_107 = 8192;
x_108 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_104);
x_109 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_107, x_104, x_108);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_111 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_106);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 2);
lean_inc(x_114);
lean_dec(x_112);
lean_ctor_set(x_33, 0, x_114);
lean_inc(x_8);
x_115 = l_Lean_Elab_Term_ensureHasType(x_33, x_104, x_8, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Elab_Term_assignExprMVar(x_5, x_116, x_8, x_117);
lean_dec(x_8);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = 1;
x_122 = lean_box(x_121);
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_120;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_119);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_8);
lean_dec(x_5);
x_124 = lean_ctor_get(x_115, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_126 = x_115;
} else {
 lean_dec_ref(x_115);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_110);
lean_dec(x_104);
lean_free_object(x_33);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_6, x_128);
lean_dec(x_6);
x_130 = lean_nat_add(x_7, x_128);
lean_dec(x_7);
x_131 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_106);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_6 = x_129;
x_7 = x_130;
x_9 = x_132;
goto _start;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_33);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_134 = lean_ctor_get(x_103, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_103, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_136 = x_103;
} else {
 lean_dec_ref(x_103);
 x_136 = lean_box(0);
}
lean_inc(x_8);
x_137 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_134);
x_138 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_135, x_98);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_140 = lean_ctor_get(x_33, 0);
lean_inc(x_140);
lean_dec(x_33);
x_141 = lean_ctor_get(x_42, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_42, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_42, 2);
lean_inc(x_143);
x_144 = lean_ctor_get(x_42, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_42, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_42, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 lean_ctor_release(x_42, 5);
 x_147 = x_42;
} else {
 lean_dec_ref(x_42);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_8, 0);
lean_inc(x_148);
x_149 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_147)) {
 x_150 = lean_alloc_ctor(0, 6, 0);
} else {
 x_150 = x_147;
}
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_142);
lean_ctor_set(x_150, 2, x_143);
lean_ctor_set(x_150, 3, x_144);
lean_ctor_set(x_150, 4, x_149);
lean_ctor_set(x_150, 5, x_146);
lean_inc(x_2);
x_151 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_140, x_148, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; size_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_8);
x_154 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_153, x_145);
x_155 = 8192;
x_156 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_152);
x_157 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_155, x_152, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_159 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_154);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 2);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_inc(x_8);
x_164 = l_Lean_Elab_Term_ensureHasType(x_163, x_152, x_8, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_Elab_Term_assignExprMVar(x_5, x_165, x_8, x_166);
lean_dec(x_8);
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
x_170 = 1;
x_171 = lean_box(x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
x_173 = lean_ctor_get(x_164, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_158);
lean_dec(x_152);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_nat_add(x_6, x_177);
lean_dec(x_6);
x_179 = lean_nat_add(x_7, x_177);
lean_dec(x_7);
x_180 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_154);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec(x_180);
x_6 = x_178;
x_7 = x_179;
x_9 = x_181;
goto _start;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_183 = lean_ctor_get(x_151, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_151, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_185 = x_151;
} else {
 lean_dec_ref(x_151);
 x_185 = lean_box(0);
}
lean_inc(x_8);
x_186 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_183);
x_187 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_41, x_184, x_145);
if (lean_is_scalar(x_185)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_185;
}
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_189 = !lean_is_exclusive(x_32);
if (x_189 == 0)
{
return x_32;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_32, 0);
x_191 = lean_ctor_get(x_32, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_32);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_28);
lean_dec(x_16);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_add(x_6, x_193);
lean_dec(x_6);
x_6 = x_194;
x_9 = x_23;
goto _start;
}
}
}
}
else
{
uint8_t x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_196 = 0;
x_197 = lean_box(x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_9);
return x_198;
}
}
}
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_8, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_101; 
x_101 = lean_ctor_get(x_1, 2);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 1)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_102, x_3, x_4, x_5, x_6);
return x_103;
}
else
{
lean_object* x_104; 
lean_dec(x_101);
x_104 = lean_box(0);
x_7 = x_104;
goto block_100;
}
block_100:
{
lean_object* x_8; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = l_PUnit_Inhabited;
x_10 = l_monadInhabited___rarg(x_2, x_9);
x_11 = l_unreachable_x21___rarg(x_10);
x_12 = lean_apply_4(x_11, x_3, x_4, x_5, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 2)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_19);
x_20 = l_Lean_Elab_Term_isExprMVarAssigned(x_19, x_5, x_6);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
lean_dec(x_3);
x_28 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_5, 9);
x_31 = l_Lean_Elab_replaceRef(x_24, x_30);
lean_dec(x_30);
lean_dec(x_24);
lean_ctor_set(x_5, 9, x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_25, x_26, x_27, x_28, x_19, x_32, x_32, x_5, x_23);
lean_dec(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_34);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_33);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_33, 0);
lean_dec(x_45);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
lean_ctor_set(x_33, 0, x_47);
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
lean_dec(x_33);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_34);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
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
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_ctor_get(x_5, 0);
x_57 = lean_ctor_get(x_5, 1);
x_58 = lean_ctor_get(x_5, 2);
x_59 = lean_ctor_get(x_5, 3);
x_60 = lean_ctor_get(x_5, 4);
x_61 = lean_ctor_get(x_5, 5);
x_62 = lean_ctor_get(x_5, 6);
x_63 = lean_ctor_get(x_5, 7);
x_64 = lean_ctor_get(x_5, 8);
x_65 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_66 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_68 = lean_ctor_get(x_5, 9);
lean_inc(x_68);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_5);
x_69 = l_Lean_Elab_replaceRef(x_24, x_68);
lean_dec(x_68);
lean_dec(x_24);
x_70 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_70, 0, x_56);
lean_ctor_set(x_70, 1, x_57);
lean_ctor_set(x_70, 2, x_58);
lean_ctor_set(x_70, 3, x_59);
lean_ctor_set(x_70, 4, x_60);
lean_ctor_set(x_70, 5, x_61);
lean_ctor_set(x_70, 6, x_62);
lean_ctor_set(x_70, 7, x_63);
lean_ctor_set(x_70, 8, x_64);
lean_ctor_set(x_70, 9, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*10, x_65);
lean_ctor_set_uint8(x_70, sizeof(void*)*10 + 1, x_66);
lean_ctor_set_uint8(x_70, sizeof(void*)*10 + 2, x_67);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_25, x_26, x_27, x_28, x_19, x_71, x_71, x_70, x_23);
lean_dec(x_27);
lean_dec(x_25);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_4);
if (lean_is_scalar(x_76)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_76;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_4);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_81 = x_72;
} else {
 lean_dec_ref(x_72);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_73);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_4);
x_85 = lean_ctor_get(x_72, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_72, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_87 = x_72;
} else {
 lean_dec_ref(x_72);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_20);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_20, 0);
lean_dec(x_90);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_4);
lean_ctor_set(x_20, 0, x_92);
return x_20;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_20, 1);
lean_inc(x_93);
lean_dec(x_20);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_4);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_4);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_6);
return x_99;
}
}
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_6(x_8, lean_box(0), x_9, x_3, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1), 6, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_1);
x_16 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1), 6, 2);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
x_17 = lean_apply_7(x_14, lean_box(0), x_15, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(x_2, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_array_push(x_14, x_1);
lean_ctor_set(x_2, 0, x_15);
x_16 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_17 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_16, x_12, x_2, x_11, x_4, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_21 = lean_array_push(x_18, x_1);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_20);
x_23 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__2;
x_24 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_23, x_12, x_22, x_11, x_4, x_10);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_7, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_7, 0, x_29);
return x_6;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_6, 0, x_32);
return x_6;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_35 = x_7;
} else {
 lean_dec_ref(x_7);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is missing");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Elab_Term_getMCtx___rarg(x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_10, x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; 
lean_free_object(x_8);
lean_dec(x_5);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_nat_dec_lt(x_1, x_2);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_4, 2);
lean_dec(x_18);
lean_inc(x_2);
lean_ctor_set(x_4, 2, x_2);
x_19 = 0;
x_20 = lean_box(x_19);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_4, x_20, x_6, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_unbox(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_2 = x_27;
x_5 = x_23;
x_7 = x_25;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = lean_unsigned_to_nat(0u);
x_2 = x_30;
x_5 = x_23;
x_7 = x_29;
goto _start;
}
}
else
{
uint8_t x_32; 
lean_dec(x_4);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
lean_inc(x_2);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_2);
x_39 = 0;
x_40 = lean_box(x_39);
lean_inc(x_6);
lean_inc(x_38);
lean_inc(x_3);
x_41 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_38, x_40, x_6, x_11);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unbox(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_2, x_46);
lean_dec(x_2);
x_2 = x_47;
x_4 = x_38;
x_5 = x_43;
x_7 = x_45;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_2);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_unsigned_to_nat(0u);
x_2 = x_50;
x_4 = x_38;
x_5 = x_43;
x_7 = x_49;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_38);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_54 = x_41;
} else {
 lean_dec_ref(x_41);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_15, 0);
lean_inc(x_56);
x_57 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_15);
lean_dec(x_15);
x_58 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_60 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Elab_Term_throwErrorAt___rarg(x_56, x_62, x_6, x_11);
lean_dec(x_56);
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
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_70 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_68, x_3);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_5);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_5);
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_75 = lean_nat_dec_lt(x_1, x_2);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_4, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_4, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_78 = x_4;
} else {
 lean_dec_ref(x_4);
 x_78 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 3, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
lean_ctor_set(x_79, 2, x_2);
x_80 = 0;
x_81 = lean_box(x_80);
lean_inc(x_6);
lean_inc(x_79);
lean_inc(x_3);
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_79, x_81, x_6, x_69);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_unbox(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_add(x_2, x_87);
lean_dec(x_2);
x_2 = x_88;
x_4 = x_79;
x_5 = x_84;
x_7 = x_86;
goto _start;
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_2);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_dec(x_82);
x_91 = lean_unsigned_to_nat(0u);
x_2 = x_91;
x_4 = x_79;
x_5 = x_84;
x_7 = x_90;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_79);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_ctor_get(x_74, 0);
lean_inc(x_97);
x_98 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_74);
lean_dec(x_74);
x_99 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_101 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_102 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_103 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Elab_Term_throwErrorAt___rarg(x_97, x_103, x_6, x_69);
lean_dec(x_97);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_4, x_7, x_1, x_8, x_10, x_2, x_3);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
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
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
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
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l___private_Lean_Elab_StructInst_5__getStructName___rarg(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
x_12 = l_Lean_isStructureLike(x_10, x_7);
lean_inc(x_7);
x_13 = l___private_Lean_Elab_StructInst_7__mkStructView(x_1, x_7, x_3);
if (x_12 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_13);
lean_dec(x_2);
x_76 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_76, 0, x_7);
x_77 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
x_80 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Elab_Term_throwError___rarg(x_80, x_4, x_11);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
return x_81;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_81);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
else
{
lean_dec(x_7);
x_14 = x_11;
goto block_75;
}
block_75:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Elab_Term_throwError___rarg(x_17, x_4, x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
lean_inc(x_4);
x_20 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_19, x_4, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_getOptions(x_4, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_27 = l_Lean_checkTraceOption(x_24, x_26);
lean_dec(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_4);
x_28 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_21, x_2, x_4, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_32, x_4, x_30);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_31);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
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
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
return x_28;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_28);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_inc(x_21);
x_46 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_21);
x_47 = l_Lean_Options_empty;
x_48 = l_Lean_Format_pretty(x_46, x_47);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = l_Lean_Elab_Term_logTrace(x_26, x_50, x_4, x_25);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_4);
x_53 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_21, x_2, x_4, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_57, x_4, x_55);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_56);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_4);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_20);
if (x_71 == 0)
{
return x_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_20, 0);
x_73 = lean_ctor_get(x_20, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_20);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_6);
if (x_86 == 0)
{
return x_6;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_6, 0);
x_88 = lean_ctor_get(x_6, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_6);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(4u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_isNone(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_5, x_7);
lean_dec(x_5);
x_9 = l_Lean_mkOptionalNode___closed__1;
x_10 = l_Lean_Syntax_setArg(x_1, x_4, x_9);
x_11 = l_Array_empty___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = l_Lean_Elab_Term_elabArrow___lambda__1___closed__4;
x_14 = lean_array_push(x_13, x_8);
x_15 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_array_push(x_11, x_16);
x_18 = l_Lean_nullKind___closed__2;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_array_push(x_12, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_25 = lean_array_push(x_23, x_24);
x_26 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, explicit source is required when using '[<index>] := <value>'");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_StructInst_elabStructInst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Elab_Term_getEnv___rarg(x_86);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
lean_dec(x_87);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_88, 5);
x_92 = lean_ctor_get(x_3, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 4);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_environment_main_module(x_89);
x_96 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_inc(x_1);
x_97 = l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(x_1, x_96, x_91);
lean_dec(x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_ctor_set(x_88, 5, x_99);
x_5 = x_98;
x_6 = x_88;
goto block_83;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_100 = lean_ctor_get(x_88, 0);
x_101 = lean_ctor_get(x_88, 1);
x_102 = lean_ctor_get(x_88, 2);
x_103 = lean_ctor_get(x_88, 3);
x_104 = lean_ctor_get(x_88, 4);
x_105 = lean_ctor_get(x_88, 5);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_88);
x_106 = lean_ctor_get(x_3, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 4);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_environment_main_module(x_89);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_85);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_inc(x_1);
x_111 = l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(x_1, x_110, x_105);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_114, 0, x_100);
lean_ctor_set(x_114, 1, x_101);
lean_ctor_set(x_114, 2, x_102);
lean_ctor_set(x_114, 3, x_103);
lean_ctor_set(x_114, 4, x_104);
lean_ctor_set(x_114, 5, x_113);
x_5 = x_112;
x_6 = x_114;
goto block_83;
}
block_83:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_7 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_3, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_3, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_3);
x_13 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_3, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_StructInst_25__elabStructInstAux(x_1, x_2, x_11, x_3, x_15);
return x_16;
}
else
{
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = l___private_Lean_Elab_StructInst_4__elabModifyOp(x_1, x_18, x_19, x_2, x_3, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_23 = l_Lean_Elab_Term_throwError___rarg(x_22, x_3, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_ctor_get(x_8, 0);
lean_inc(x_33);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_3, 7);
lean_inc(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_3, 7, x_37);
x_38 = 1;
x_39 = l_Lean_Elab_Term_elabTerm(x_33, x_2, x_38, x_3, x_32);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_ctor_get(x_3, 3);
x_44 = lean_ctor_get(x_3, 4);
x_45 = lean_ctor_get(x_3, 5);
x_46 = lean_ctor_get(x_3, 6);
x_47 = lean_ctor_get(x_3, 7);
x_48 = lean_ctor_get(x_3, 8);
x_49 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_50 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_51 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_52 = lean_ctor_get(x_3, 9);
lean_inc(x_52);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
lean_inc(x_33);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_33);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
x_55 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_55, 0, x_40);
lean_ctor_set(x_55, 1, x_41);
lean_ctor_set(x_55, 2, x_42);
lean_ctor_set(x_55, 3, x_43);
lean_ctor_set(x_55, 4, x_44);
lean_ctor_set(x_55, 5, x_45);
lean_ctor_set(x_55, 6, x_46);
lean_ctor_set(x_55, 7, x_54);
lean_ctor_set(x_55, 8, x_48);
lean_ctor_set(x_55, 9, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*10, x_49);
lean_ctor_set_uint8(x_55, sizeof(void*)*10 + 1, x_50);
lean_ctor_set_uint8(x_55, sizeof(void*)*10 + 2, x_51);
x_56 = 1;
x_57 = l_Lean_Elab_Term_elabTerm(x_33, x_2, x_56, x_55, x_32);
return x_57;
}
}
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_5, 0);
lean_inc(x_58);
lean_dec(x_5);
x_59 = !lean_is_exclusive(x_3);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_3, 7);
lean_inc(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_3, 7, x_62);
x_63 = 1;
x_64 = l_Lean_Elab_Term_elabTerm(x_58, x_2, x_63, x_3, x_6);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_65 = lean_ctor_get(x_3, 0);
x_66 = lean_ctor_get(x_3, 1);
x_67 = lean_ctor_get(x_3, 2);
x_68 = lean_ctor_get(x_3, 3);
x_69 = lean_ctor_get(x_3, 4);
x_70 = lean_ctor_get(x_3, 5);
x_71 = lean_ctor_get(x_3, 6);
x_72 = lean_ctor_get(x_3, 7);
x_73 = lean_ctor_get(x_3, 8);
x_74 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_75 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
x_77 = lean_ctor_get(x_3, 9);
lean_inc(x_77);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_3);
lean_inc(x_58);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_58);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_72);
x_80 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_80, 0, x_65);
lean_ctor_set(x_80, 1, x_66);
lean_ctor_set(x_80, 2, x_67);
lean_ctor_set(x_80, 3, x_68);
lean_ctor_set(x_80, 4, x_69);
lean_ctor_set(x_80, 5, x_70);
lean_ctor_set(x_80, 6, x_71);
lean_ctor_set(x_80, 7, x_79);
lean_ctor_set(x_80, 8, x_73);
lean_ctor_set(x_80, 9, x_77);
lean_ctor_set_uint8(x_80, sizeof(void*)*10, x_74);
lean_ctor_set_uint8(x_80, sizeof(void*)*10 + 1, x_75);
lean_ctor_set_uint8(x_80, sizeof(void*)*10 + 2, x_76);
x_81 = 1;
x_82 = l_Lean_Elab_Term_elabTerm(x_58, x_2, x_81, x_80, x_6);
return x_82;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_elabStructInst), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Term_termElabAttribute;
x_3 = l_Lean_Parser_Term_structInst___elambda__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_StructInst_27__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_FindExpr(lean_object*);
lean_object* initialize_Lean_Elab_App(lean_object*);
lean_object* initialize_Lean_Elab_Binders(lean_object*);
lean_object* initialize_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_StructInst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FindExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_App(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Binders(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3);
l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4 = _init_l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4);
l_Lean_Elab_Term_StructInst_Source_inhabited = _init_l_Lean_Elab_Term_StructInst_Source_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Source_inhabited);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__1 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__1);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__2 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__2);
l___private_Lean_Elab_StructInst_2__getStructSource___closed__3 = _init_l___private_Lean_Elab_StructInst_2__getStructSource___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_2__getStructSource___closed__3);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__22);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27);
l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28 = _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28();
lean_mark_persistent(l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5);
l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6 = _init_l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_FieldLHS_inhabited = _init_l_Lean_Elab_Term_StructInst_FieldLHS_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_FieldLHS_inhabited);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2 = _init_l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2);
l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_inhabited___closed__1);
l_Lean_Elab_Term_StructInst_Struct_inhabited = _init_l_Lean_Elab_Term_StructInst_Struct_inhabited();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_inhabited);
l_Lean_Elab_Term_StructInst_formatField___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__1);
l_Lean_Elab_Term_StructInst_formatField___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__2);
l_Lean_Elab_Term_StructInst_formatField___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__3);
l_Lean_Elab_Term_StructInst_formatField___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatField___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatField___closed__4);
l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1 = _init_l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4);
l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5 = _init_l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5);
l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasFormat = _init_l_Lean_Elab_Term_StructInst_Struct_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasFormat);
l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Struct_hasToString = _init_l_Lean_Elab_Term_StructInst_Struct_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Struct_hasToString);
l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasFormat = _init_l_Lean_Elab_Term_StructInst_Field_hasFormat();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasFormat);
l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1 = _init_l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1);
l_Lean_Elab_Term_StructInst_Field_hasToString = _init_l_Lean_Elab_Term_StructInst_Field_hasToString();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_Field_hasToString);
l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1 = _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1);
l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2 = _init_l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1);
l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1 = _init_l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8);
l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__8);
l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6);
l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1 = _init_l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__2);
l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3 = _init_l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2);
l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3 = _init_l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2);
l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3 = _init_l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3);
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
l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6 = _init_l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2);
l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3 = _init_l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3();
lean_mark_persistent(l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2);
l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3 = _init_l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5);
l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6 = _init_l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6();
lean_mark_persistent(l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6);
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
res = l___private_Lean_Elab_StructInst_27__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
