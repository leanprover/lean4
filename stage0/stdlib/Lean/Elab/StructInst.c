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
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
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
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
extern lean_object* l_Lean_Meta_mkId___closed__2;
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
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
extern lean_object* l_Lean_Parser_Term_letDecl___closed__2;
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
extern lean_object* l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
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
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 8);
lean_dec(x_11);
lean_ctor_set(x_2, 8, x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_5, x_12);
lean_inc(x_13);
x_14 = l_Lean_Elab_Term_isLocalIdent_x3f(x_13, x_2, x_3);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_getMainModule___rarg(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_24 = l_Lean_addMacroScope(x_21, x_23, x_18);
x_25 = lean_box(0);
x_26 = l_Lean_SourceInfo_inhabited___closed__1;
x_27 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_28 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
x_29 = l_Lean_Syntax_setArg(x_5, x_12, x_28);
x_30 = l_Lean_Syntax_setArg(x_1, x_4, x_29);
x_31 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_22);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_getMainModule___rarg(x_33);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_addMacroScope(x_36, x_23, x_32);
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_27);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_25);
x_39 = l_Array_empty___closed__1;
x_40 = lean_array_push(x_39, x_38);
x_41 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_42 = lean_array_push(x_40, x_41);
x_43 = lean_array_push(x_42, x_41);
x_44 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_array_push(x_45, x_13);
x_47 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = lean_array_push(x_39, x_48);
x_50 = l_Lean_Parser_Term_letDecl___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_53 = lean_array_push(x_52, x_51);
x_54 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_30);
x_57 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_34, 0, x_59);
return x_34;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_60 = lean_ctor_get(x_34, 0);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_34);
x_62 = l_Lean_addMacroScope(x_60, x_23, x_32);
x_63 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_27);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_25);
x_64 = l_Array_empty___closed__1;
x_65 = lean_array_push(x_64, x_63);
x_66 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_67 = lean_array_push(x_65, x_66);
x_68 = lean_array_push(x_67, x_66);
x_69 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_70 = lean_array_push(x_68, x_69);
x_71 = lean_array_push(x_70, x_13);
x_72 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_push(x_64, x_73);
x_75 = l_Lean_Parser_Term_letDecl___closed__2;
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
x_77 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_78 = lean_array_push(x_77, x_76);
x_79 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_array_push(x_80, x_30);
x_82 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_61);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_14);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_14, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_14, 0, x_88);
return x_14;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_14, 1);
lean_inc(x_89);
lean_dec(x_14);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_92 = lean_ctor_get(x_2, 0);
x_93 = lean_ctor_get(x_2, 1);
x_94 = lean_ctor_get(x_2, 2);
x_95 = lean_ctor_get(x_2, 3);
x_96 = lean_ctor_get(x_2, 4);
x_97 = lean_ctor_get(x_2, 5);
x_98 = lean_ctor_get(x_2, 6);
x_99 = lean_ctor_get(x_2, 7);
x_100 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_101 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_102 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_103 = lean_ctor_get(x_2, 9);
lean_inc(x_103);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_2);
x_104 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_93);
lean_ctor_set(x_104, 2, x_94);
lean_ctor_set(x_104, 3, x_95);
lean_ctor_set(x_104, 4, x_96);
lean_ctor_set(x_104, 5, x_97);
lean_ctor_set(x_104, 6, x_98);
lean_ctor_set(x_104, 7, x_99);
lean_ctor_set(x_104, 8, x_8);
lean_ctor_set(x_104, 9, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*10, x_100);
lean_ctor_set_uint8(x_104, sizeof(void*)*10 + 1, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*10 + 2, x_102);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Syntax_getArg(x_5, x_105);
lean_inc(x_106);
x_107 = l_Lean_Elab_Term_isLocalIdent_x3f(x_106, x_104, x_3);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_Elab_Term_getCurrMacroScope(x_104, x_109);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = l_Lean_Elab_Term_getMainModule___rarg(x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_117 = l_Lean_addMacroScope(x_114, x_116, x_111);
x_118 = lean_box(0);
x_119 = l_Lean_SourceInfo_inhabited___closed__1;
x_120 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_121 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set(x_121, 2, x_117);
lean_ctor_set(x_121, 3, x_118);
x_122 = l_Lean_Syntax_setArg(x_5, x_105, x_121);
x_123 = l_Lean_Syntax_setArg(x_1, x_4, x_122);
x_124 = l_Lean_Elab_Term_getCurrMacroScope(x_104, x_115);
lean_dec(x_104);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Elab_Term_getMainModule___rarg(x_126);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = l_Lean_addMacroScope(x_128, x_116, x_125);
x_132 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_132, 0, x_119);
lean_ctor_set(x_132, 1, x_120);
lean_ctor_set(x_132, 2, x_131);
lean_ctor_set(x_132, 3, x_118);
x_133 = l_Array_empty___closed__1;
x_134 = lean_array_push(x_133, x_132);
x_135 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_136 = lean_array_push(x_134, x_135);
x_137 = lean_array_push(x_136, x_135);
x_138 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_139 = lean_array_push(x_137, x_138);
x_140 = lean_array_push(x_139, x_106);
x_141 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_133, x_142);
x_144 = l_Lean_Parser_Term_letDecl___closed__2;
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_147 = lean_array_push(x_146, x_145);
x_148 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_149 = lean_array_push(x_147, x_148);
x_150 = lean_array_push(x_149, x_123);
x_151 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
if (lean_is_scalar(x_130)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_130;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_129);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_108);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_5);
lean_dec(x_1);
x_155 = lean_ctor_get(x_107, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_156 = x_107;
} else {
 lean_dec_ref(x_107);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_3);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_161 = lean_ctor_get(x_3, 0);
x_162 = lean_ctor_get(x_3, 1);
x_163 = lean_ctor_get(x_3, 2);
x_164 = lean_ctor_get(x_3, 3);
x_165 = lean_ctor_get(x_3, 4);
x_166 = lean_ctor_get(x_3, 5);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_3);
x_167 = lean_nat_add(x_166, x_4);
x_168 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_168, 0, x_161);
lean_ctor_set(x_168, 1, x_162);
lean_ctor_set(x_168, 2, x_163);
lean_ctor_set(x_168, 3, x_164);
lean_ctor_set(x_168, 4, x_165);
lean_ctor_set(x_168, 5, x_167);
if (x_6 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_169 = lean_ctor_get(x_2, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 2);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 3);
lean_inc(x_172);
x_173 = lean_ctor_get(x_2, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_2, 5);
lean_inc(x_174);
x_175 = lean_ctor_get(x_2, 6);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 7);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_178 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_179 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_180 = lean_ctor_get(x_2, 9);
lean_inc(x_180);
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
 x_181 = x_2;
} else {
 lean_dec_ref(x_2);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(0, 10, 3);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_169);
lean_ctor_set(x_182, 1, x_170);
lean_ctor_set(x_182, 2, x_171);
lean_ctor_set(x_182, 3, x_172);
lean_ctor_set(x_182, 4, x_173);
lean_ctor_set(x_182, 5, x_174);
lean_ctor_set(x_182, 6, x_175);
lean_ctor_set(x_182, 7, x_176);
lean_ctor_set(x_182, 8, x_166);
lean_ctor_set(x_182, 9, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*10, x_177);
lean_ctor_set_uint8(x_182, sizeof(void*)*10 + 1, x_178);
lean_ctor_set_uint8(x_182, sizeof(void*)*10 + 2, x_179);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Lean_Syntax_getArg(x_5, x_183);
lean_inc(x_184);
x_185 = l_Lean_Elab_Term_isLocalIdent_x3f(x_184, x_182, x_168);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = l_Lean_Elab_Term_getCurrMacroScope(x_182, x_187);
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
x_200 = l_Lean_Syntax_setArg(x_5, x_183, x_199);
x_201 = l_Lean_Syntax_setArg(x_1, x_4, x_200);
x_202 = l_Lean_Elab_Term_getCurrMacroScope(x_182, x_193);
lean_dec(x_182);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = l_Lean_Elab_Term_getMainModule___rarg(x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = l_Lean_addMacroScope(x_206, x_194, x_203);
x_210 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_210, 0, x_197);
lean_ctor_set(x_210, 1, x_198);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_196);
x_211 = l_Array_empty___closed__1;
x_212 = lean_array_push(x_211, x_210);
x_213 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_214 = lean_array_push(x_212, x_213);
x_215 = lean_array_push(x_214, x_213);
x_216 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_217 = lean_array_push(x_215, x_216);
x_218 = lean_array_push(x_217, x_184);
x_219 = l_Lean_Parser_Term_letIdDecl___elambda__1___closed__2;
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_array_push(x_211, x_220);
x_222 = l_Lean_Parser_Term_letDecl___closed__2;
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
x_224 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_225 = lean_array_push(x_224, x_223);
x_226 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_227 = lean_array_push(x_225, x_226);
x_228 = lean_array_push(x_227, x_201);
x_229 = l_Lean_Parser_Term_let___elambda__1___closed__2;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_231, 0, x_230);
if (lean_is_scalar(x_208)) {
 x_232 = lean_alloc_ctor(0, 2, 0);
} else {
 x_232 = x_208;
}
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_207);
return x_232;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_186);
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_5);
lean_dec(x_1);
x_233 = lean_ctor_get(x_185, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_234 = x_185;
} else {
 lean_dec_ref(x_185);
 x_234 = lean_box(0);
}
x_235 = lean_box(0);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
return x_236;
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_166);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_168);
return x_238;
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
lean_object* x_66; 
x_66 = lean_box(0);
x_9 = x_66;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = l_Lean_Syntax_isNone(x_7);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_9 = x_68;
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_3);
return x_70;
}
}
block_65:
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_5, x_16);
x_18 = l_Lean_Elab_Term_isLocalIdent_x3f(x_17, x_2, x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_22 = l_unreachable_x21___rarg(x_21);
x_23 = lean_apply_2(x_22, x_2, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 0);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_ctor_get(x_19, 0);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_2, 3);
x_36 = lean_ctor_get(x_2, 4);
x_37 = lean_ctor_get(x_2, 5);
x_38 = lean_ctor_get(x_2, 6);
x_39 = lean_ctor_get(x_2, 7);
x_40 = lean_ctor_get(x_2, 8);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_43 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_44 = lean_ctor_get(x_2, 9);
lean_inc(x_44);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
x_45 = l_Lean_Elab_replaceRef(x_1, x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_46, 0, x_32);
lean_ctor_set(x_46, 1, x_33);
lean_ctor_set(x_46, 2, x_34);
lean_ctor_set(x_46, 3, x_35);
lean_ctor_set(x_46, 4, x_36);
lean_ctor_set(x_46, 5, x_37);
lean_ctor_set(x_46, 6, x_38);
lean_ctor_set(x_46, 7, x_39);
lean_ctor_set(x_46, 8, x_40);
lean_ctor_set(x_46, 9, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*10, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 1, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*10 + 2, x_43);
x_47 = l_Lean_Syntax_isNone(x_7);
lean_dec(x_7);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
x_48 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_49 = l_Lean_Elab_Term_throwError___rarg(x_48, x_46, x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_5, x_50);
x_52 = l_Lean_Elab_Term_isLocalIdent_x3f(x_51, x_46, x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_5);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_56 = l_unreachable_x21___rarg(x_55);
x_57 = lean_apply_2(x_56, x_46, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_53, 0);
lean_inc(x_60);
lean_dec(x_53);
x_61 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_5);
lean_dec(x_2);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_7);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
return x_64;
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
lean_object* x_7; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_275 = l_Lean_Elab_Term_getOptions(x_5, x_6);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_279 = l_Lean_checkTraceOption(x_276, x_278);
lean_dec(x_276);
if (x_279 == 0)
{
x_7 = x_277;
goto block_274;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_inc(x_2);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_2);
x_281 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28;
x_282 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
lean_inc(x_3);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_3);
x_284 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Lean_Elab_Term_logTrace(x_278, x_284, x_5, x_277);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_7 = x_286;
goto block_274;
}
block_274:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Syntax_isNone(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_11 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_getMainModule___rarg(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_18 = l_Lean_addMacroScope(x_15, x_17, x_12);
x_19 = lean_box(0);
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_22 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_9, x_23);
lean_inc(x_24);
x_25 = l_Lean_Syntax_getKind(x_24);
x_26 = l_Lean_Parser_Term_structInstArrayRef___elambda__1___closed__2;
x_27 = lean_name_eq(x_25, x_26);
lean_dec(x_25);
x_28 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_29 = lean_array_get_size(x_28);
x_30 = l_Array_extract___rarg(x_28, x_8, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = l_Lean_nullKind;
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_Lean_Elab_Term_getOptions(x_5, x_16);
if (x_27 == 0)
{
lean_object* x_167; 
x_167 = l_Lean_Syntax_getArg(x_24, x_8);
lean_dec(x_24);
x_34 = x_167;
goto block_166;
}
else
{
x_34 = x_24;
goto block_166;
}
block_166:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_2);
x_35 = l_Lean_Syntax_setArg(x_2, x_23, x_34);
x_36 = l_Lean_Syntax_setArg(x_35, x_8, x_32);
x_37 = l_Lean_mkOptionalNode___closed__2;
x_38 = lean_array_push(x_37, x_36);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_157 = lean_ctor_get(x_3, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_3, 1);
lean_inc(x_158);
x_159 = lean_array_get_size(x_158);
x_160 = lean_nat_dec_lt(x_23, x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; 
lean_dec(x_22);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_158);
x_40 = x_161;
goto block_156;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_162 = lean_box(0);
x_163 = lean_array_fset(x_158, x_23, x_162);
x_164 = lean_array_fset(x_163, x_23, x_22);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_157);
lean_ctor_set(x_165, 1, x_164);
x_40 = x_165;
goto block_156;
}
}
else
{
lean_dec(x_22);
lean_inc(x_3);
x_40 = x_3;
goto block_156;
}
block_156:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_inc(x_1);
x_41 = l_Lean_Syntax_setArg(x_1, x_8, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_setArg(x_41, x_42, x_39);
x_145 = lean_ctor_get(x_33, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_33, 1);
lean_inc(x_146);
lean_dec(x_33);
x_147 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_148 = l_Lean_checkTraceOption(x_145, x_147);
lean_dec(x_145);
if (x_148 == 0)
{
x_44 = x_146;
goto block_144;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_inc(x_1);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_1);
x_150 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
x_151 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_inc(x_43);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_43);
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Elab_Term_logTrace(x_147, x_153, x_5, x_146);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_44 = x_155;
goto block_144;
}
block_144:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_45 = l_Lean_Syntax_getArg(x_2, x_23);
lean_dec(x_2);
x_46 = l_Lean_Syntax_getArg(x_45, x_8);
lean_dec(x_45);
x_47 = l_Lean_Syntax_getArg(x_3, x_23);
lean_dec(x_3);
x_48 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_44);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Elab_Term_getMainModule___rarg(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Array_empty___closed__1;
x_55 = lean_array_push(x_54, x_47);
x_56 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_57 = lean_array_push(x_55, x_56);
x_58 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_inc(x_49);
lean_inc(x_52);
x_59 = l_Lean_addMacroScope(x_52, x_58, x_49);
x_60 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
x_61 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
x_62 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_62, 0, x_20);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_59);
lean_ctor_set(x_62, 3, x_61);
x_63 = lean_array_push(x_57, x_62);
x_64 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_array_push(x_54, x_65);
x_67 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_inc(x_49);
lean_inc(x_52);
x_68 = l_Lean_addMacroScope(x_52, x_67, x_49);
x_69 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_70 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_70, 0, x_20);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_70, 2, x_68);
lean_ctor_set(x_70, 3, x_19);
x_71 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_72 = lean_array_push(x_71, x_70);
x_73 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_74 = lean_array_push(x_72, x_73);
x_75 = lean_array_push(x_74, x_46);
x_76 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_77 = lean_array_push(x_75, x_76);
x_78 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = lean_array_push(x_54, x_79);
x_81 = l_Lean_addMacroScope(x_52, x_17, x_49);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_20);
lean_ctor_set(x_82, 1, x_21);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_19);
x_83 = lean_array_push(x_54, x_82);
x_84 = l_Lean_nullKind___closed__2;
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
x_86 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_87 = lean_array_push(x_86, x_85);
x_88 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_89 = lean_array_push(x_87, x_88);
x_90 = lean_array_push(x_89, x_43);
x_91 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_push(x_54, x_92);
x_94 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_95 = lean_array_push(x_93, x_94);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_84);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_array_push(x_71, x_96);
x_98 = lean_array_push(x_97, x_76);
x_99 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_array_push(x_80, x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_84);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_array_push(x_66, x_102);
x_104 = l_Lean_mkAppStx___closed__8;
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_132 = l_Lean_Elab_Term_getOptions(x_5, x_53);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_136 = l_Lean_checkTraceOption(x_133, x_135);
lean_dec(x_133);
if (x_136 == 0)
{
x_106 = x_134;
goto block_131;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_inc(x_1);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_1);
x_138 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_inc(x_105);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_105);
x_141 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Elab_Term_logTrace(x_135, x_141, x_5, x_134);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_106 = x_143;
goto block_131;
}
block_131:
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_5);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_5, 7);
lean_inc(x_105);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_105);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_5, 7, x_110);
x_111 = 1;
x_112 = l_Lean_Elab_Term_elabTerm(x_105, x_4, x_111, x_5, x_106);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_113 = lean_ctor_get(x_5, 0);
x_114 = lean_ctor_get(x_5, 1);
x_115 = lean_ctor_get(x_5, 2);
x_116 = lean_ctor_get(x_5, 3);
x_117 = lean_ctor_get(x_5, 4);
x_118 = lean_ctor_get(x_5, 5);
x_119 = lean_ctor_get(x_5, 6);
x_120 = lean_ctor_get(x_5, 7);
x_121 = lean_ctor_get(x_5, 8);
x_122 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_123 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_124 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_125 = lean_ctor_get(x_5, 9);
lean_inc(x_125);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_5);
lean_inc(x_105);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_105);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_120);
x_128 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_128, 0, x_113);
lean_ctor_set(x_128, 1, x_114);
lean_ctor_set(x_128, 2, x_115);
lean_ctor_set(x_128, 3, x_116);
lean_ctor_set(x_128, 4, x_117);
lean_ctor_set(x_128, 5, x_118);
lean_ctor_set(x_128, 6, x_119);
lean_ctor_set(x_128, 7, x_127);
lean_ctor_set(x_128, 8, x_121);
lean_ctor_set(x_128, 9, x_125);
lean_ctor_set_uint8(x_128, sizeof(void*)*10, x_122);
lean_ctor_set_uint8(x_128, sizeof(void*)*10 + 1, x_123);
lean_ctor_set_uint8(x_128, sizeof(void*)*10 + 2, x_124);
x_129 = 1;
x_130 = l_Lean_Elab_Term_elabTerm(x_105, x_4, x_129, x_128, x_106);
return x_130;
}
}
}
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_9);
x_168 = lean_unsigned_to_nat(3u);
x_169 = l_Lean_Syntax_getArg(x_2, x_168);
x_170 = lean_unsigned_to_nat(0u);
x_171 = l_Lean_Syntax_getArg(x_2, x_170);
lean_dec(x_2);
x_172 = l_Lean_Syntax_getArg(x_171, x_8);
lean_dec(x_171);
x_173 = l_Lean_Syntax_getArg(x_3, x_170);
lean_dec(x_3);
x_174 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_7);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
x_177 = l_Lean_Elab_Term_getMainModule___rarg(x_176);
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = l_Array_empty___closed__1;
x_181 = lean_array_push(x_180, x_173);
x_182 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_183 = lean_array_push(x_181, x_182);
x_184 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_inc(x_175);
lean_inc(x_178);
x_185 = l_Lean_addMacroScope(x_178, x_184, x_175);
x_186 = lean_box(0);
x_187 = l_Lean_SourceInfo_inhabited___closed__1;
x_188 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
x_189 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
x_190 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
lean_ctor_set(x_190, 2, x_185);
lean_ctor_set(x_190, 3, x_189);
x_191 = lean_array_push(x_183, x_190);
x_192 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = lean_array_push(x_180, x_193);
x_195 = l___private_Lean_Elab_App_18__elabAppLValsAux___main___closed__2;
lean_inc(x_175);
lean_inc(x_178);
x_196 = l_Lean_addMacroScope(x_178, x_195, x_175);
x_197 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_198 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_198, 0, x_187);
lean_ctor_set(x_198, 1, x_197);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_186);
x_199 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_200 = lean_array_push(x_199, x_198);
x_201 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_202 = lean_array_push(x_200, x_201);
x_203 = lean_array_push(x_202, x_172);
x_204 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_205 = lean_array_push(x_203, x_204);
x_206 = l_Lean_Parser_Term_namedArgument___elambda__1___closed__2;
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_208 = lean_array_push(x_180, x_207);
x_209 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_210 = l_Lean_addMacroScope(x_178, x_209, x_175);
x_211 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_187);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_210);
lean_ctor_set(x_212, 3, x_186);
x_213 = lean_array_push(x_180, x_212);
x_214 = l_Lean_nullKind___closed__2;
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_213);
x_216 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_217 = lean_array_push(x_216, x_215);
x_218 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_219 = lean_array_push(x_217, x_218);
x_220 = lean_array_push(x_219, x_169);
x_221 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_220);
x_223 = lean_array_push(x_180, x_222);
x_224 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_225 = lean_array_push(x_223, x_224);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_214);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_push(x_199, x_226);
x_228 = lean_array_push(x_227, x_204);
x_229 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_array_push(x_208, x_230);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_214);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_array_push(x_194, x_232);
x_234 = l_Lean_mkAppStx___closed__8;
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_262 = l_Lean_Elab_Term_getOptions(x_5, x_179);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_266 = l_Lean_checkTraceOption(x_263, x_265);
lean_dec(x_263);
if (x_266 == 0)
{
x_236 = x_264;
goto block_261;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_inc(x_1);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_1);
x_268 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_269 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
lean_inc(x_235);
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_235);
x_271 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_Elab_Term_logTrace(x_265, x_271, x_5, x_264);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
x_236 = x_273;
goto block_261;
}
block_261:
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_5);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; 
x_238 = lean_ctor_get(x_5, 7);
lean_inc(x_235);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_1);
lean_ctor_set(x_239, 1, x_235);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_238);
lean_ctor_set(x_5, 7, x_240);
x_241 = 1;
x_242 = l_Lean_Elab_Term_elabTerm(x_235, x_4, x_241, x_5, x_236);
return x_242;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; uint8_t x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
x_243 = lean_ctor_get(x_5, 0);
x_244 = lean_ctor_get(x_5, 1);
x_245 = lean_ctor_get(x_5, 2);
x_246 = lean_ctor_get(x_5, 3);
x_247 = lean_ctor_get(x_5, 4);
x_248 = lean_ctor_get(x_5, 5);
x_249 = lean_ctor_get(x_5, 6);
x_250 = lean_ctor_get(x_5, 7);
x_251 = lean_ctor_get(x_5, 8);
x_252 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_253 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_254 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_255 = lean_ctor_get(x_5, 9);
lean_inc(x_255);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_5);
lean_inc(x_235);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_1);
lean_ctor_set(x_256, 1, x_235);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_250);
x_258 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_258, 0, x_243);
lean_ctor_set(x_258, 1, x_244);
lean_ctor_set(x_258, 2, x_245);
lean_ctor_set(x_258, 3, x_246);
lean_ctor_set(x_258, 4, x_247);
lean_ctor_set(x_258, 5, x_248);
lean_ctor_set(x_258, 6, x_249);
lean_ctor_set(x_258, 7, x_257);
lean_ctor_set(x_258, 8, x_251);
lean_ctor_set(x_258, 9, x_255);
lean_ctor_set_uint8(x_258, sizeof(void*)*10, x_252);
lean_ctor_set_uint8(x_258, sizeof(void*)*10 + 1, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*10 + 2, x_254);
x_259 = 1;
x_260 = l_Lean_Elab_Term_elabTerm(x_235, x_4, x_259, x_258, x_236);
return x_260;
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
lean_inc(x_3);
lean_inc(x_1);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_3);
lean_inc(x_28);
x_30 = l_Lean_Elab_Term_tryPostponeIfMVar(x_28, x_3, x_29);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_41; 
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 0);
lean_dec(x_33);
x_41 = l_Lean_Expr_getAppFn___main(x_28);
if (lean_obj_tag(x_41) == 4)
{
lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_3);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_ctor_set(x_30, 0, x_42);
return x_30;
}
else
{
lean_object* x_43; 
lean_dec(x_41);
lean_free_object(x_30);
x_43 = lean_box(0);
x_34 = x_43;
goto block_40;
}
block_40:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_28);
x_36 = l_Lean_indentExpr(x_35);
x_37 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Elab_Term_throwError___rarg(x_38, x_3, x_32);
return x_39;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_52; 
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_dec(x_30);
x_52 = l_Lean_Expr_getAppFn___main(x_28);
if (lean_obj_tag(x_52) == 4)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_28);
lean_dec(x_3);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_44);
return x_54;
}
else
{
lean_object* x_55; 
lean_dec(x_52);
x_55 = lean_box(0);
x_45 = x_55;
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
uint8_t x_56; 
lean_dec(x_28);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
return x_30;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
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
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; 
lean_dec(x_2);
x_68 = lean_box(0);
x_7 = x_68;
goto block_22;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_69);
x_70 = l_Lean_Elab_Term_whnf(x_69, x_3, x_6);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_81; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_70, 1);
x_81 = l_Lean_Expr_getAppFn___main(x_72);
lean_dec(x_72);
switch (lean_obj_tag(x_81)) {
case 0:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_69);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
lean_inc(x_3);
x_83 = l_Lean_Elab_Term_inferType(x_82, x_3, x_73);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_3);
x_86 = l_Lean_Elab_Term_whnf(x_84, x_3, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_3);
lean_inc(x_87);
x_89 = l_Lean_Elab_Term_tryPostponeIfMVar(x_87, x_3, x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_100; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_100 = l_Lean_Expr_getAppFn___main(x_87);
if (lean_obj_tag(x_100) == 4)
{
lean_object* x_101; 
lean_dec(x_87);
lean_dec(x_3);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
lean_ctor_set(x_89, 0, x_101);
return x_89;
}
else
{
lean_object* x_102; 
lean_dec(x_100);
lean_free_object(x_89);
x_102 = lean_box(0);
x_93 = x_102;
goto block_99;
}
block_99:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_93);
x_94 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_94, 0, x_87);
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
lean_object* x_103; lean_object* x_104; lean_object* x_111; 
x_103 = lean_ctor_get(x_89, 1);
lean_inc(x_103);
lean_dec(x_89);
x_111 = l_Lean_Expr_getAppFn___main(x_87);
if (lean_obj_tag(x_111) == 4)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_87);
lean_dec(x_3);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_103);
return x_113;
}
else
{
lean_object* x_114; 
lean_dec(x_111);
x_114 = lean_box(0);
x_104 = x_114;
goto block_110;
}
block_110:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_104);
x_105 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_105, 0, x_87);
x_106 = l_Lean_indentExpr(x_105);
x_107 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_Term_throwError___rarg(x_108, x_3, x_103);
return x_109;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_87);
lean_dec(x_3);
x_115 = !lean_is_exclusive(x_89);
if (x_115 == 0)
{
return x_89;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_89, 0);
x_117 = lean_ctor_get(x_89, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_89);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_86);
if (x_119 == 0)
{
return x_86;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_86, 0);
x_121 = lean_ctor_get(x_86, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_86);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_83);
if (x_123 == 0)
{
return x_83;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_83, 0);
x_125 = lean_ctor_get(x_83, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_83);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_2);
x_127 = lean_box(0);
x_74 = x_127;
goto block_80;
}
}
case 1:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_69);
x_128 = lean_ctor_get(x_2, 1);
lean_inc(x_128);
lean_dec(x_2);
lean_inc(x_3);
x_129 = l_Lean_Elab_Term_inferType(x_128, x_3, x_73);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_3);
x_132 = l_Lean_Elab_Term_whnf(x_130, x_3, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_3);
lean_inc(x_133);
x_135 = l_Lean_Elab_Term_tryPostponeIfMVar(x_133, x_3, x_134);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_146; 
x_137 = lean_ctor_get(x_135, 1);
x_138 = lean_ctor_get(x_135, 0);
lean_dec(x_138);
x_146 = l_Lean_Expr_getAppFn___main(x_133);
if (lean_obj_tag(x_146) == 4)
{
lean_object* x_147; 
lean_dec(x_133);
lean_dec(x_3);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec(x_146);
lean_ctor_set(x_135, 0, x_147);
return x_135;
}
else
{
lean_object* x_148; 
lean_dec(x_146);
lean_free_object(x_135);
x_148 = lean_box(0);
x_139 = x_148;
goto block_145;
}
block_145:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_139);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_133);
x_141 = l_Lean_indentExpr(x_140);
x_142 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_143 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_141);
x_144 = l_Lean_Elab_Term_throwError___rarg(x_143, x_3, x_137);
return x_144;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_157; 
x_149 = lean_ctor_get(x_135, 1);
lean_inc(x_149);
lean_dec(x_135);
x_157 = l_Lean_Expr_getAppFn___main(x_133);
if (lean_obj_tag(x_157) == 4)
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_133);
lean_dec(x_3);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec(x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_149);
return x_159;
}
else
{
lean_object* x_160; 
lean_dec(x_157);
x_160 = lean_box(0);
x_150 = x_160;
goto block_156;
}
block_156:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_150);
x_151 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_151, 0, x_133);
x_152 = l_Lean_indentExpr(x_151);
x_153 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Elab_Term_throwError___rarg(x_154, x_3, x_149);
return x_155;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_133);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_135);
if (x_161 == 0)
{
return x_135;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_135, 0);
x_163 = lean_ctor_get(x_135, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_135);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_132);
if (x_165 == 0)
{
return x_132;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_132, 0);
x_167 = lean_ctor_get(x_132, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_132);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_3);
x_169 = !lean_is_exclusive(x_129);
if (x_169 == 0)
{
return x_129;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_129, 0);
x_171 = lean_ctor_get(x_129, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_129);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; 
lean_dec(x_2);
x_173 = lean_box(0);
x_74 = x_173;
goto block_80;
}
}
case 2:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_69);
x_174 = lean_ctor_get(x_2, 1);
lean_inc(x_174);
lean_dec(x_2);
lean_inc(x_3);
x_175 = l_Lean_Elab_Term_inferType(x_174, x_3, x_73);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
lean_inc(x_3);
x_178 = l_Lean_Elab_Term_whnf(x_176, x_3, x_177);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
lean_inc(x_3);
lean_inc(x_179);
x_181 = l_Lean_Elab_Term_tryPostponeIfMVar(x_179, x_3, x_180);
if (lean_obj_tag(x_181) == 0)
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_192; 
x_183 = lean_ctor_get(x_181, 1);
x_184 = lean_ctor_get(x_181, 0);
lean_dec(x_184);
x_192 = l_Lean_Expr_getAppFn___main(x_179);
if (lean_obj_tag(x_192) == 4)
{
lean_object* x_193; 
lean_dec(x_179);
lean_dec(x_3);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
lean_ctor_set(x_181, 0, x_193);
return x_181;
}
else
{
lean_object* x_194; 
lean_dec(x_192);
lean_free_object(x_181);
x_194 = lean_box(0);
x_185 = x_194;
goto block_191;
}
block_191:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_185);
x_186 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_186, 0, x_179);
x_187 = l_Lean_indentExpr(x_186);
x_188 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_189 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
x_190 = l_Lean_Elab_Term_throwError___rarg(x_189, x_3, x_183);
return x_190;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_203; 
x_195 = lean_ctor_get(x_181, 1);
lean_inc(x_195);
lean_dec(x_181);
x_203 = l_Lean_Expr_getAppFn___main(x_179);
if (lean_obj_tag(x_203) == 4)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_179);
lean_dec(x_3);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec(x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_195);
return x_205;
}
else
{
lean_object* x_206; 
lean_dec(x_203);
x_206 = lean_box(0);
x_196 = x_206;
goto block_202;
}
block_202:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_196);
x_197 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_197, 0, x_179);
x_198 = l_Lean_indentExpr(x_197);
x_199 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_200 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Lean_Elab_Term_throwError___rarg(x_200, x_3, x_195);
return x_201;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_179);
lean_dec(x_3);
x_207 = !lean_is_exclusive(x_181);
if (x_207 == 0)
{
return x_181;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_181, 0);
x_209 = lean_ctor_get(x_181, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_181);
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
x_211 = !lean_is_exclusive(x_178);
if (x_211 == 0)
{
return x_178;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_178, 0);
x_213 = lean_ctor_get(x_178, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_178);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_3);
x_215 = !lean_is_exclusive(x_175);
if (x_215 == 0)
{
return x_175;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_175, 0);
x_217 = lean_ctor_get(x_175, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_175);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; 
lean_dec(x_2);
x_219 = lean_box(0);
x_74 = x_219;
goto block_80;
}
}
case 3:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_69);
x_220 = lean_ctor_get(x_2, 1);
lean_inc(x_220);
lean_dec(x_2);
lean_inc(x_3);
x_221 = l_Lean_Elab_Term_inferType(x_220, x_3, x_73);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
lean_inc(x_3);
x_224 = l_Lean_Elab_Term_whnf(x_222, x_3, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
lean_inc(x_3);
lean_inc(x_225);
x_227 = l_Lean_Elab_Term_tryPostponeIfMVar(x_225, x_3, x_226);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_238; 
x_229 = lean_ctor_get(x_227, 1);
x_230 = lean_ctor_get(x_227, 0);
lean_dec(x_230);
x_238 = l_Lean_Expr_getAppFn___main(x_225);
if (lean_obj_tag(x_238) == 4)
{
lean_object* x_239; 
lean_dec(x_225);
lean_dec(x_3);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec(x_238);
lean_ctor_set(x_227, 0, x_239);
return x_227;
}
else
{
lean_object* x_240; 
lean_dec(x_238);
lean_free_object(x_227);
x_240 = lean_box(0);
x_231 = x_240;
goto block_237;
}
block_237:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_231);
x_232 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_232, 0, x_225);
x_233 = l_Lean_indentExpr(x_232);
x_234 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_235 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_233);
x_236 = l_Lean_Elab_Term_throwError___rarg(x_235, x_3, x_229);
return x_236;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_249; 
x_241 = lean_ctor_get(x_227, 1);
lean_inc(x_241);
lean_dec(x_227);
x_249 = l_Lean_Expr_getAppFn___main(x_225);
if (lean_obj_tag(x_249) == 4)
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_225);
lean_dec(x_3);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
lean_dec(x_249);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_241);
return x_251;
}
else
{
lean_object* x_252; 
lean_dec(x_249);
x_252 = lean_box(0);
x_242 = x_252;
goto block_248;
}
block_248:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_242);
x_243 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_243, 0, x_225);
x_244 = l_Lean_indentExpr(x_243);
x_245 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_246 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = l_Lean_Elab_Term_throwError___rarg(x_246, x_3, x_241);
return x_247;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_225);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_227);
if (x_253 == 0)
{
return x_227;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_227, 0);
x_255 = lean_ctor_get(x_227, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_227);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_3);
x_257 = !lean_is_exclusive(x_224);
if (x_257 == 0)
{
return x_224;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_224, 0);
x_259 = lean_ctor_get(x_224, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_224);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_3);
x_261 = !lean_is_exclusive(x_221);
if (x_261 == 0)
{
return x_221;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_221, 0);
x_263 = lean_ctor_get(x_221, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_221);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; 
lean_dec(x_2);
x_265 = lean_box(0);
x_74 = x_265;
goto block_80;
}
}
case 4:
{
lean_object* x_266; 
lean_dec(x_69);
lean_dec(x_3);
lean_dec(x_2);
x_266 = lean_ctor_get(x_81, 0);
lean_inc(x_266);
lean_dec(x_81);
lean_ctor_set(x_70, 0, x_266);
return x_70;
}
case 5:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_69);
x_267 = lean_ctor_get(x_2, 1);
lean_inc(x_267);
lean_dec(x_2);
lean_inc(x_3);
x_268 = l_Lean_Elab_Term_inferType(x_267, x_3, x_73);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_3);
x_271 = l_Lean_Elab_Term_whnf(x_269, x_3, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
lean_inc(x_3);
lean_inc(x_272);
x_274 = l_Lean_Elab_Term_tryPostponeIfMVar(x_272, x_3, x_273);
if (lean_obj_tag(x_274) == 0)
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_285; 
x_276 = lean_ctor_get(x_274, 1);
x_277 = lean_ctor_get(x_274, 0);
lean_dec(x_277);
x_285 = l_Lean_Expr_getAppFn___main(x_272);
if (lean_obj_tag(x_285) == 4)
{
lean_object* x_286; 
lean_dec(x_272);
lean_dec(x_3);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
lean_dec(x_285);
lean_ctor_set(x_274, 0, x_286);
return x_274;
}
else
{
lean_object* x_287; 
lean_dec(x_285);
lean_free_object(x_274);
x_287 = lean_box(0);
x_278 = x_287;
goto block_284;
}
block_284:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_278);
x_279 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_279, 0, x_272);
x_280 = l_Lean_indentExpr(x_279);
x_281 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_282 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
x_283 = l_Lean_Elab_Term_throwError___rarg(x_282, x_3, x_276);
return x_283;
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_296; 
x_288 = lean_ctor_get(x_274, 1);
lean_inc(x_288);
lean_dec(x_274);
x_296 = l_Lean_Expr_getAppFn___main(x_272);
if (lean_obj_tag(x_296) == 4)
{
lean_object* x_297; lean_object* x_298; 
lean_dec(x_272);
lean_dec(x_3);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_dec(x_296);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_298, 1, x_288);
return x_298;
}
else
{
lean_object* x_299; 
lean_dec(x_296);
x_299 = lean_box(0);
x_289 = x_299;
goto block_295;
}
block_295:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_289);
x_290 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_290, 0, x_272);
x_291 = l_Lean_indentExpr(x_290);
x_292 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_293 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
x_294 = l_Lean_Elab_Term_throwError___rarg(x_293, x_3, x_288);
return x_294;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_272);
lean_dec(x_3);
x_300 = !lean_is_exclusive(x_274);
if (x_300 == 0)
{
return x_274;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_274, 0);
x_302 = lean_ctor_get(x_274, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_274);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
else
{
uint8_t x_304; 
lean_dec(x_3);
x_304 = !lean_is_exclusive(x_271);
if (x_304 == 0)
{
return x_271;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_271, 0);
x_306 = lean_ctor_get(x_271, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_271);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
return x_307;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_3);
x_308 = !lean_is_exclusive(x_268);
if (x_308 == 0)
{
return x_268;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_268, 0);
x_310 = lean_ctor_get(x_268, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_268);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
lean_object* x_312; 
lean_dec(x_2);
x_312 = lean_box(0);
x_74 = x_312;
goto block_80;
}
}
case 6:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_313; lean_object* x_314; 
lean_dec(x_69);
x_313 = lean_ctor_get(x_2, 1);
lean_inc(x_313);
lean_dec(x_2);
lean_inc(x_3);
x_314 = l_Lean_Elab_Term_inferType(x_313, x_3, x_73);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_3);
x_317 = l_Lean_Elab_Term_whnf(x_315, x_3, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
lean_inc(x_3);
lean_inc(x_318);
x_320 = l_Lean_Elab_Term_tryPostponeIfMVar(x_318, x_3, x_319);
if (lean_obj_tag(x_320) == 0)
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_331; 
x_322 = lean_ctor_get(x_320, 1);
x_323 = lean_ctor_get(x_320, 0);
lean_dec(x_323);
x_331 = l_Lean_Expr_getAppFn___main(x_318);
if (lean_obj_tag(x_331) == 4)
{
lean_object* x_332; 
lean_dec(x_318);
lean_dec(x_3);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
lean_dec(x_331);
lean_ctor_set(x_320, 0, x_332);
return x_320;
}
else
{
lean_object* x_333; 
lean_dec(x_331);
lean_free_object(x_320);
x_333 = lean_box(0);
x_324 = x_333;
goto block_330;
}
block_330:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_324);
x_325 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_325, 0, x_318);
x_326 = l_Lean_indentExpr(x_325);
x_327 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_328 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_326);
x_329 = l_Lean_Elab_Term_throwError___rarg(x_328, x_3, x_322);
return x_329;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_342; 
x_334 = lean_ctor_get(x_320, 1);
lean_inc(x_334);
lean_dec(x_320);
x_342 = l_Lean_Expr_getAppFn___main(x_318);
if (lean_obj_tag(x_342) == 4)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_318);
lean_dec(x_3);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
lean_dec(x_342);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_334);
return x_344;
}
else
{
lean_object* x_345; 
lean_dec(x_342);
x_345 = lean_box(0);
x_335 = x_345;
goto block_341;
}
block_341:
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_335);
x_336 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_336, 0, x_318);
x_337 = l_Lean_indentExpr(x_336);
x_338 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_339 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
x_340 = l_Lean_Elab_Term_throwError___rarg(x_339, x_3, x_334);
return x_340;
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_318);
lean_dec(x_3);
x_346 = !lean_is_exclusive(x_320);
if (x_346 == 0)
{
return x_320;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_320, 0);
x_348 = lean_ctor_get(x_320, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_320);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_3);
x_350 = !lean_is_exclusive(x_317);
if (x_350 == 0)
{
return x_317;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_317, 0);
x_352 = lean_ctor_get(x_317, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_317);
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
lean_dec(x_3);
x_354 = !lean_is_exclusive(x_314);
if (x_354 == 0)
{
return x_314;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_314, 0);
x_356 = lean_ctor_get(x_314, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_314);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; 
lean_dec(x_2);
x_358 = lean_box(0);
x_74 = x_358;
goto block_80;
}
}
case 7:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_359; lean_object* x_360; 
lean_dec(x_69);
x_359 = lean_ctor_get(x_2, 1);
lean_inc(x_359);
lean_dec(x_2);
lean_inc(x_3);
x_360 = l_Lean_Elab_Term_inferType(x_359, x_3, x_73);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
lean_inc(x_3);
x_363 = l_Lean_Elab_Term_whnf(x_361, x_3, x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
lean_inc(x_3);
lean_inc(x_364);
x_366 = l_Lean_Elab_Term_tryPostponeIfMVar(x_364, x_3, x_365);
if (lean_obj_tag(x_366) == 0)
{
uint8_t x_367; 
x_367 = !lean_is_exclusive(x_366);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_377; 
x_368 = lean_ctor_get(x_366, 1);
x_369 = lean_ctor_get(x_366, 0);
lean_dec(x_369);
x_377 = l_Lean_Expr_getAppFn___main(x_364);
if (lean_obj_tag(x_377) == 4)
{
lean_object* x_378; 
lean_dec(x_364);
lean_dec(x_3);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec(x_377);
lean_ctor_set(x_366, 0, x_378);
return x_366;
}
else
{
lean_object* x_379; 
lean_dec(x_377);
lean_free_object(x_366);
x_379 = lean_box(0);
x_370 = x_379;
goto block_376;
}
block_376:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_370);
x_371 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_371, 0, x_364);
x_372 = l_Lean_indentExpr(x_371);
x_373 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_374 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_372);
x_375 = l_Lean_Elab_Term_throwError___rarg(x_374, x_3, x_368);
return x_375;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_388; 
x_380 = lean_ctor_get(x_366, 1);
lean_inc(x_380);
lean_dec(x_366);
x_388 = l_Lean_Expr_getAppFn___main(x_364);
if (lean_obj_tag(x_388) == 4)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_364);
lean_dec(x_3);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
lean_dec(x_388);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_380);
return x_390;
}
else
{
lean_object* x_391; 
lean_dec(x_388);
x_391 = lean_box(0);
x_381 = x_391;
goto block_387;
}
block_387:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec(x_381);
x_382 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_382, 0, x_364);
x_383 = l_Lean_indentExpr(x_382);
x_384 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_385 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Lean_Elab_Term_throwError___rarg(x_385, x_3, x_380);
return x_386;
}
}
}
else
{
uint8_t x_392; 
lean_dec(x_364);
lean_dec(x_3);
x_392 = !lean_is_exclusive(x_366);
if (x_392 == 0)
{
return x_366;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_366, 0);
x_394 = lean_ctor_get(x_366, 1);
lean_inc(x_394);
lean_inc(x_393);
lean_dec(x_366);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_3);
x_396 = !lean_is_exclusive(x_363);
if (x_396 == 0)
{
return x_363;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_363, 0);
x_398 = lean_ctor_get(x_363, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_363);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
uint8_t x_400; 
lean_dec(x_3);
x_400 = !lean_is_exclusive(x_360);
if (x_400 == 0)
{
return x_360;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_360, 0);
x_402 = lean_ctor_get(x_360, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_360);
x_403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
else
{
lean_object* x_404; 
lean_dec(x_2);
x_404 = lean_box(0);
x_74 = x_404;
goto block_80;
}
}
case 8:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_405; lean_object* x_406; 
lean_dec(x_69);
x_405 = lean_ctor_get(x_2, 1);
lean_inc(x_405);
lean_dec(x_2);
lean_inc(x_3);
x_406 = l_Lean_Elab_Term_inferType(x_405, x_3, x_73);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
lean_inc(x_3);
x_409 = l_Lean_Elab_Term_whnf(x_407, x_3, x_408);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_3);
lean_inc(x_410);
x_412 = l_Lean_Elab_Term_tryPostponeIfMVar(x_410, x_3, x_411);
if (lean_obj_tag(x_412) == 0)
{
uint8_t x_413; 
x_413 = !lean_is_exclusive(x_412);
if (x_413 == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_423; 
x_414 = lean_ctor_get(x_412, 1);
x_415 = lean_ctor_get(x_412, 0);
lean_dec(x_415);
x_423 = l_Lean_Expr_getAppFn___main(x_410);
if (lean_obj_tag(x_423) == 4)
{
lean_object* x_424; 
lean_dec(x_410);
lean_dec(x_3);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
lean_dec(x_423);
lean_ctor_set(x_412, 0, x_424);
return x_412;
}
else
{
lean_object* x_425; 
lean_dec(x_423);
lean_free_object(x_412);
x_425 = lean_box(0);
x_416 = x_425;
goto block_422;
}
block_422:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_416);
x_417 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_417, 0, x_410);
x_418 = l_Lean_indentExpr(x_417);
x_419 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_420 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_418);
x_421 = l_Lean_Elab_Term_throwError___rarg(x_420, x_3, x_414);
return x_421;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_434; 
x_426 = lean_ctor_get(x_412, 1);
lean_inc(x_426);
lean_dec(x_412);
x_434 = l_Lean_Expr_getAppFn___main(x_410);
if (lean_obj_tag(x_434) == 4)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_410);
lean_dec(x_3);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
lean_dec(x_434);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_426);
return x_436;
}
else
{
lean_object* x_437; 
lean_dec(x_434);
x_437 = lean_box(0);
x_427 = x_437;
goto block_433;
}
block_433:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_427);
x_428 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_428, 0, x_410);
x_429 = l_Lean_indentExpr(x_428);
x_430 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_431 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = l_Lean_Elab_Term_throwError___rarg(x_431, x_3, x_426);
return x_432;
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_410);
lean_dec(x_3);
x_438 = !lean_is_exclusive(x_412);
if (x_438 == 0)
{
return x_412;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_412, 0);
x_440 = lean_ctor_get(x_412, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_412);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
else
{
uint8_t x_442; 
lean_dec(x_3);
x_442 = !lean_is_exclusive(x_409);
if (x_442 == 0)
{
return x_409;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_409, 0);
x_444 = lean_ctor_get(x_409, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_409);
x_445 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
return x_445;
}
}
}
else
{
uint8_t x_446; 
lean_dec(x_3);
x_446 = !lean_is_exclusive(x_406);
if (x_446 == 0)
{
return x_406;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_447 = lean_ctor_get(x_406, 0);
x_448 = lean_ctor_get(x_406, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_406);
x_449 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_449, 0, x_447);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
else
{
lean_object* x_450; 
lean_dec(x_2);
x_450 = lean_box(0);
x_74 = x_450;
goto block_80;
}
}
case 9:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_69);
x_451 = lean_ctor_get(x_2, 1);
lean_inc(x_451);
lean_dec(x_2);
lean_inc(x_3);
x_452 = l_Lean_Elab_Term_inferType(x_451, x_3, x_73);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
lean_inc(x_3);
x_455 = l_Lean_Elab_Term_whnf(x_453, x_3, x_454);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
lean_inc(x_3);
lean_inc(x_456);
x_458 = l_Lean_Elab_Term_tryPostponeIfMVar(x_456, x_3, x_457);
if (lean_obj_tag(x_458) == 0)
{
uint8_t x_459; 
x_459 = !lean_is_exclusive(x_458);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_469; 
x_460 = lean_ctor_get(x_458, 1);
x_461 = lean_ctor_get(x_458, 0);
lean_dec(x_461);
x_469 = l_Lean_Expr_getAppFn___main(x_456);
if (lean_obj_tag(x_469) == 4)
{
lean_object* x_470; 
lean_dec(x_456);
lean_dec(x_3);
x_470 = lean_ctor_get(x_469, 0);
lean_inc(x_470);
lean_dec(x_469);
lean_ctor_set(x_458, 0, x_470);
return x_458;
}
else
{
lean_object* x_471; 
lean_dec(x_469);
lean_free_object(x_458);
x_471 = lean_box(0);
x_462 = x_471;
goto block_468;
}
block_468:
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_462);
x_463 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_463, 0, x_456);
x_464 = l_Lean_indentExpr(x_463);
x_465 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_466 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
x_467 = l_Lean_Elab_Term_throwError___rarg(x_466, x_3, x_460);
return x_467;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_480; 
x_472 = lean_ctor_get(x_458, 1);
lean_inc(x_472);
lean_dec(x_458);
x_480 = l_Lean_Expr_getAppFn___main(x_456);
if (lean_obj_tag(x_480) == 4)
{
lean_object* x_481; lean_object* x_482; 
lean_dec(x_456);
lean_dec(x_3);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
lean_dec(x_480);
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_472);
return x_482;
}
else
{
lean_object* x_483; 
lean_dec(x_480);
x_483 = lean_box(0);
x_473 = x_483;
goto block_479;
}
block_479:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_473);
x_474 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_474, 0, x_456);
x_475 = l_Lean_indentExpr(x_474);
x_476 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_477 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_477, 0, x_476);
lean_ctor_set(x_477, 1, x_475);
x_478 = l_Lean_Elab_Term_throwError___rarg(x_477, x_3, x_472);
return x_478;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_456);
lean_dec(x_3);
x_484 = !lean_is_exclusive(x_458);
if (x_484 == 0)
{
return x_458;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_458, 0);
x_486 = lean_ctor_get(x_458, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_458);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_3);
x_488 = !lean_is_exclusive(x_455);
if (x_488 == 0)
{
return x_455;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_455, 0);
x_490 = lean_ctor_get(x_455, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_455);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
else
{
uint8_t x_492; 
lean_dec(x_3);
x_492 = !lean_is_exclusive(x_452);
if (x_492 == 0)
{
return x_452;
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_452, 0);
x_494 = lean_ctor_get(x_452, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_452);
x_495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_495, 0, x_493);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
else
{
lean_object* x_496; 
lean_dec(x_2);
x_496 = lean_box(0);
x_74 = x_496;
goto block_80;
}
}
case 10:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_497; lean_object* x_498; 
lean_dec(x_69);
x_497 = lean_ctor_get(x_2, 1);
lean_inc(x_497);
lean_dec(x_2);
lean_inc(x_3);
x_498 = l_Lean_Elab_Term_inferType(x_497, x_3, x_73);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
lean_inc(x_3);
x_501 = l_Lean_Elab_Term_whnf(x_499, x_3, x_500);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
lean_inc(x_3);
lean_inc(x_502);
x_504 = l_Lean_Elab_Term_tryPostponeIfMVar(x_502, x_3, x_503);
if (lean_obj_tag(x_504) == 0)
{
uint8_t x_505; 
x_505 = !lean_is_exclusive(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_515; 
x_506 = lean_ctor_get(x_504, 1);
x_507 = lean_ctor_get(x_504, 0);
lean_dec(x_507);
x_515 = l_Lean_Expr_getAppFn___main(x_502);
if (lean_obj_tag(x_515) == 4)
{
lean_object* x_516; 
lean_dec(x_502);
lean_dec(x_3);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec(x_515);
lean_ctor_set(x_504, 0, x_516);
return x_504;
}
else
{
lean_object* x_517; 
lean_dec(x_515);
lean_free_object(x_504);
x_517 = lean_box(0);
x_508 = x_517;
goto block_514;
}
block_514:
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_508);
x_509 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_509, 0, x_502);
x_510 = l_Lean_indentExpr(x_509);
x_511 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_512 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_510);
x_513 = l_Lean_Elab_Term_throwError___rarg(x_512, x_3, x_506);
return x_513;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_526; 
x_518 = lean_ctor_get(x_504, 1);
lean_inc(x_518);
lean_dec(x_504);
x_526 = l_Lean_Expr_getAppFn___main(x_502);
if (lean_obj_tag(x_526) == 4)
{
lean_object* x_527; lean_object* x_528; 
lean_dec(x_502);
lean_dec(x_3);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
lean_dec(x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_518);
return x_528;
}
else
{
lean_object* x_529; 
lean_dec(x_526);
x_529 = lean_box(0);
x_519 = x_529;
goto block_525;
}
block_525:
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_519);
x_520 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_520, 0, x_502);
x_521 = l_Lean_indentExpr(x_520);
x_522 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_523 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_521);
x_524 = l_Lean_Elab_Term_throwError___rarg(x_523, x_3, x_518);
return x_524;
}
}
}
else
{
uint8_t x_530; 
lean_dec(x_502);
lean_dec(x_3);
x_530 = !lean_is_exclusive(x_504);
if (x_530 == 0)
{
return x_504;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_504, 0);
x_532 = lean_ctor_get(x_504, 1);
lean_inc(x_532);
lean_inc(x_531);
lean_dec(x_504);
x_533 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
}
else
{
uint8_t x_534; 
lean_dec(x_3);
x_534 = !lean_is_exclusive(x_501);
if (x_534 == 0)
{
return x_501;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_535 = lean_ctor_get(x_501, 0);
x_536 = lean_ctor_get(x_501, 1);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_501);
x_537 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_537, 0, x_535);
lean_ctor_set(x_537, 1, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
lean_dec(x_3);
x_538 = !lean_is_exclusive(x_498);
if (x_538 == 0)
{
return x_498;
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_498, 0);
x_540 = lean_ctor_get(x_498, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_498);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_539);
lean_ctor_set(x_541, 1, x_540);
return x_541;
}
}
}
else
{
lean_object* x_542; 
lean_dec(x_2);
x_542 = lean_box(0);
x_74 = x_542;
goto block_80;
}
}
case 11:
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_543; lean_object* x_544; 
lean_dec(x_69);
x_543 = lean_ctor_get(x_2, 1);
lean_inc(x_543);
lean_dec(x_2);
lean_inc(x_3);
x_544 = l_Lean_Elab_Term_inferType(x_543, x_3, x_73);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
lean_inc(x_3);
x_547 = l_Lean_Elab_Term_whnf(x_545, x_3, x_546);
if (lean_obj_tag(x_547) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
lean_inc(x_3);
lean_inc(x_548);
x_550 = l_Lean_Elab_Term_tryPostponeIfMVar(x_548, x_3, x_549);
if (lean_obj_tag(x_550) == 0)
{
uint8_t x_551; 
x_551 = !lean_is_exclusive(x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_561; 
x_552 = lean_ctor_get(x_550, 1);
x_553 = lean_ctor_get(x_550, 0);
lean_dec(x_553);
x_561 = l_Lean_Expr_getAppFn___main(x_548);
if (lean_obj_tag(x_561) == 4)
{
lean_object* x_562; 
lean_dec(x_548);
lean_dec(x_3);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
lean_dec(x_561);
lean_ctor_set(x_550, 0, x_562);
return x_550;
}
else
{
lean_object* x_563; 
lean_dec(x_561);
lean_free_object(x_550);
x_563 = lean_box(0);
x_554 = x_563;
goto block_560;
}
block_560:
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_554);
x_555 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_555, 0, x_548);
x_556 = l_Lean_indentExpr(x_555);
x_557 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_558 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_556);
x_559 = l_Lean_Elab_Term_throwError___rarg(x_558, x_3, x_552);
return x_559;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_572; 
x_564 = lean_ctor_get(x_550, 1);
lean_inc(x_564);
lean_dec(x_550);
x_572 = l_Lean_Expr_getAppFn___main(x_548);
if (lean_obj_tag(x_572) == 4)
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_548);
lean_dec(x_3);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
lean_dec(x_572);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_564);
return x_574;
}
else
{
lean_object* x_575; 
lean_dec(x_572);
x_575 = lean_box(0);
x_565 = x_575;
goto block_571;
}
block_571:
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
lean_dec(x_565);
x_566 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_566, 0, x_548);
x_567 = l_Lean_indentExpr(x_566);
x_568 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_569 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_567);
x_570 = l_Lean_Elab_Term_throwError___rarg(x_569, x_3, x_564);
return x_570;
}
}
}
else
{
uint8_t x_576; 
lean_dec(x_548);
lean_dec(x_3);
x_576 = !lean_is_exclusive(x_550);
if (x_576 == 0)
{
return x_550;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_577 = lean_ctor_get(x_550, 0);
x_578 = lean_ctor_get(x_550, 1);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_550);
x_579 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
return x_579;
}
}
}
else
{
uint8_t x_580; 
lean_dec(x_3);
x_580 = !lean_is_exclusive(x_547);
if (x_580 == 0)
{
return x_547;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_581 = lean_ctor_get(x_547, 0);
x_582 = lean_ctor_get(x_547, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_547);
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
lean_dec(x_3);
x_584 = !lean_is_exclusive(x_544);
if (x_584 == 0)
{
return x_544;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_544, 0);
x_586 = lean_ctor_get(x_544, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_544);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
else
{
lean_object* x_588; 
lean_dec(x_2);
x_588 = lean_box(0);
x_74 = x_588;
goto block_80;
}
}
default: 
{
lean_dec(x_81);
lean_free_object(x_70);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_69);
x_589 = lean_ctor_get(x_2, 1);
lean_inc(x_589);
lean_dec(x_2);
lean_inc(x_3);
x_590 = l_Lean_Elab_Term_inferType(x_589, x_3, x_73);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_590, 1);
lean_inc(x_592);
lean_dec(x_590);
lean_inc(x_3);
x_593 = l_Lean_Elab_Term_whnf(x_591, x_3, x_592);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec(x_593);
lean_inc(x_3);
lean_inc(x_594);
x_596 = l_Lean_Elab_Term_tryPostponeIfMVar(x_594, x_3, x_595);
if (lean_obj_tag(x_596) == 0)
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_607; 
x_598 = lean_ctor_get(x_596, 1);
x_599 = lean_ctor_get(x_596, 0);
lean_dec(x_599);
x_607 = l_Lean_Expr_getAppFn___main(x_594);
if (lean_obj_tag(x_607) == 4)
{
lean_object* x_608; 
lean_dec(x_594);
lean_dec(x_3);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
lean_dec(x_607);
lean_ctor_set(x_596, 0, x_608);
return x_596;
}
else
{
lean_object* x_609; 
lean_dec(x_607);
lean_free_object(x_596);
x_609 = lean_box(0);
x_600 = x_609;
goto block_606;
}
block_606:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_600);
x_601 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_601, 0, x_594);
x_602 = l_Lean_indentExpr(x_601);
x_603 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_604 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_602);
x_605 = l_Lean_Elab_Term_throwError___rarg(x_604, x_3, x_598);
return x_605;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_618; 
x_610 = lean_ctor_get(x_596, 1);
lean_inc(x_610);
lean_dec(x_596);
x_618 = l_Lean_Expr_getAppFn___main(x_594);
if (lean_obj_tag(x_618) == 4)
{
lean_object* x_619; lean_object* x_620; 
lean_dec(x_594);
lean_dec(x_3);
x_619 = lean_ctor_get(x_618, 0);
lean_inc(x_619);
lean_dec(x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_610);
return x_620;
}
else
{
lean_object* x_621; 
lean_dec(x_618);
x_621 = lean_box(0);
x_611 = x_621;
goto block_617;
}
block_617:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
lean_dec(x_611);
x_612 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_612, 0, x_594);
x_613 = l_Lean_indentExpr(x_612);
x_614 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_615 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_613);
x_616 = l_Lean_Elab_Term_throwError___rarg(x_615, x_3, x_610);
return x_616;
}
}
}
else
{
uint8_t x_622; 
lean_dec(x_594);
lean_dec(x_3);
x_622 = !lean_is_exclusive(x_596);
if (x_622 == 0)
{
return x_596;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_596, 0);
x_624 = lean_ctor_get(x_596, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_596);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
}
else
{
uint8_t x_626; 
lean_dec(x_3);
x_626 = !lean_is_exclusive(x_593);
if (x_626 == 0)
{
return x_593;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_593, 0);
x_628 = lean_ctor_get(x_593, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_593);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
else
{
uint8_t x_630; 
lean_dec(x_3);
x_630 = !lean_is_exclusive(x_590);
if (x_630 == 0)
{
return x_590;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_590, 0);
x_632 = lean_ctor_get(x_590, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_590);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
else
{
lean_object* x_634; 
lean_dec(x_2);
x_634 = lean_box(0);
x_74 = x_634;
goto block_80;
}
}
}
block_80:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_74);
x_75 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_75, 0, x_69);
x_76 = l_Lean_indentExpr(x_75);
x_77 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_Elab_Term_throwError___rarg(x_78, x_3, x_73);
return x_79;
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_644; 
x_635 = lean_ctor_get(x_70, 0);
x_636 = lean_ctor_get(x_70, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_70);
x_644 = l_Lean_Expr_getAppFn___main(x_635);
lean_dec(x_635);
switch (lean_obj_tag(x_644)) {
case 0:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_69);
x_645 = lean_ctor_get(x_2, 1);
lean_inc(x_645);
lean_dec(x_2);
lean_inc(x_3);
x_646 = l_Lean_Elab_Term_inferType(x_645, x_3, x_636);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_646, 1);
lean_inc(x_648);
lean_dec(x_646);
lean_inc(x_3);
x_649 = l_Lean_Elab_Term_whnf(x_647, x_3, x_648);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
lean_dec(x_649);
lean_inc(x_3);
lean_inc(x_650);
x_652 = l_Lean_Elab_Term_tryPostponeIfMVar(x_650, x_3, x_651);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_662; 
x_653 = lean_ctor_get(x_652, 1);
lean_inc(x_653);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_654 = x_652;
} else {
 lean_dec_ref(x_652);
 x_654 = lean_box(0);
}
x_662 = l_Lean_Expr_getAppFn___main(x_650);
if (lean_obj_tag(x_662) == 4)
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_650);
lean_dec(x_3);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
lean_dec(x_662);
if (lean_is_scalar(x_654)) {
 x_664 = lean_alloc_ctor(0, 2, 0);
} else {
 x_664 = x_654;
}
lean_ctor_set(x_664, 0, x_663);
lean_ctor_set(x_664, 1, x_653);
return x_664;
}
else
{
lean_object* x_665; 
lean_dec(x_662);
lean_dec(x_654);
x_665 = lean_box(0);
x_655 = x_665;
goto block_661;
}
block_661:
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_655);
x_656 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_656, 0, x_650);
x_657 = l_Lean_indentExpr(x_656);
x_658 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_659 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_657);
x_660 = l_Lean_Elab_Term_throwError___rarg(x_659, x_3, x_653);
return x_660;
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_650);
lean_dec(x_3);
x_666 = lean_ctor_get(x_652, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_652, 1);
lean_inc(x_667);
if (lean_is_exclusive(x_652)) {
 lean_ctor_release(x_652, 0);
 lean_ctor_release(x_652, 1);
 x_668 = x_652;
} else {
 lean_dec_ref(x_652);
 x_668 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_668;
}
lean_ctor_set(x_669, 0, x_666);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_3);
x_670 = lean_ctor_get(x_649, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_649, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_672 = x_649;
} else {
 lean_dec_ref(x_649);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_3);
x_674 = lean_ctor_get(x_646, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_646, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_646)) {
 lean_ctor_release(x_646, 0);
 lean_ctor_release(x_646, 1);
 x_676 = x_646;
} else {
 lean_dec_ref(x_646);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_674);
lean_ctor_set(x_677, 1, x_675);
return x_677;
}
}
else
{
lean_object* x_678; 
lean_dec(x_2);
x_678 = lean_box(0);
x_637 = x_678;
goto block_643;
}
}
case 1:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_69);
x_679 = lean_ctor_get(x_2, 1);
lean_inc(x_679);
lean_dec(x_2);
lean_inc(x_3);
x_680 = l_Lean_Elab_Term_inferType(x_679, x_3, x_636);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
lean_inc(x_3);
x_683 = l_Lean_Elab_Term_whnf(x_681, x_3, x_682);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
lean_dec(x_683);
lean_inc(x_3);
lean_inc(x_684);
x_686 = l_Lean_Elab_Term_tryPostponeIfMVar(x_684, x_3, x_685);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_696; 
x_687 = lean_ctor_get(x_686, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_688 = x_686;
} else {
 lean_dec_ref(x_686);
 x_688 = lean_box(0);
}
x_696 = l_Lean_Expr_getAppFn___main(x_684);
if (lean_obj_tag(x_696) == 4)
{
lean_object* x_697; lean_object* x_698; 
lean_dec(x_684);
lean_dec(x_3);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
lean_dec(x_696);
if (lean_is_scalar(x_688)) {
 x_698 = lean_alloc_ctor(0, 2, 0);
} else {
 x_698 = x_688;
}
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_687);
return x_698;
}
else
{
lean_object* x_699; 
lean_dec(x_696);
lean_dec(x_688);
x_699 = lean_box(0);
x_689 = x_699;
goto block_695;
}
block_695:
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_689);
x_690 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_690, 0, x_684);
x_691 = l_Lean_indentExpr(x_690);
x_692 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_693 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_691);
x_694 = l_Lean_Elab_Term_throwError___rarg(x_693, x_3, x_687);
return x_694;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
lean_dec(x_684);
lean_dec(x_3);
x_700 = lean_ctor_get(x_686, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_686, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_702 = x_686;
} else {
 lean_dec_ref(x_686);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(1, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec(x_3);
x_704 = lean_ctor_get(x_683, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_683, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_706 = x_683;
} else {
 lean_dec_ref(x_683);
 x_706 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(1, 2, 0);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_704);
lean_ctor_set(x_707, 1, x_705);
return x_707;
}
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_3);
x_708 = lean_ctor_get(x_680, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_680, 1);
lean_inc(x_709);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_710 = x_680;
} else {
 lean_dec_ref(x_680);
 x_710 = lean_box(0);
}
if (lean_is_scalar(x_710)) {
 x_711 = lean_alloc_ctor(1, 2, 0);
} else {
 x_711 = x_710;
}
lean_ctor_set(x_711, 0, x_708);
lean_ctor_set(x_711, 1, x_709);
return x_711;
}
}
else
{
lean_object* x_712; 
lean_dec(x_2);
x_712 = lean_box(0);
x_637 = x_712;
goto block_643;
}
}
case 2:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_713; lean_object* x_714; 
lean_dec(x_69);
x_713 = lean_ctor_get(x_2, 1);
lean_inc(x_713);
lean_dec(x_2);
lean_inc(x_3);
x_714 = l_Lean_Elab_Term_inferType(x_713, x_3, x_636);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_714, 1);
lean_inc(x_716);
lean_dec(x_714);
lean_inc(x_3);
x_717 = l_Lean_Elab_Term_whnf(x_715, x_3, x_716);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
lean_inc(x_3);
lean_inc(x_718);
x_720 = l_Lean_Elab_Term_tryPostponeIfMVar(x_718, x_3, x_719);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_730; 
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_722 = x_720;
} else {
 lean_dec_ref(x_720);
 x_722 = lean_box(0);
}
x_730 = l_Lean_Expr_getAppFn___main(x_718);
if (lean_obj_tag(x_730) == 4)
{
lean_object* x_731; lean_object* x_732; 
lean_dec(x_718);
lean_dec(x_3);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
lean_dec(x_730);
if (lean_is_scalar(x_722)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_722;
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_721);
return x_732;
}
else
{
lean_object* x_733; 
lean_dec(x_730);
lean_dec(x_722);
x_733 = lean_box(0);
x_723 = x_733;
goto block_729;
}
block_729:
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_723);
x_724 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_724, 0, x_718);
x_725 = l_Lean_indentExpr(x_724);
x_726 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_727 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_725);
x_728 = l_Lean_Elab_Term_throwError___rarg(x_727, x_3, x_721);
return x_728;
}
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_718);
lean_dec(x_3);
x_734 = lean_ctor_get(x_720, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_720, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_736 = x_720;
} else {
 lean_dec_ref(x_720);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_735);
return x_737;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_3);
x_738 = lean_ctor_get(x_717, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_717, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_740 = x_717;
} else {
 lean_dec_ref(x_717);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
return x_741;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_3);
x_742 = lean_ctor_get(x_714, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_714, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_744 = x_714;
} else {
 lean_dec_ref(x_714);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
else
{
lean_object* x_746; 
lean_dec(x_2);
x_746 = lean_box(0);
x_637 = x_746;
goto block_643;
}
}
case 3:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_747; lean_object* x_748; 
lean_dec(x_69);
x_747 = lean_ctor_get(x_2, 1);
lean_inc(x_747);
lean_dec(x_2);
lean_inc(x_3);
x_748 = l_Lean_Elab_Term_inferType(x_747, x_3, x_636);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
lean_dec(x_748);
lean_inc(x_3);
x_751 = l_Lean_Elab_Term_whnf(x_749, x_3, x_750);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
lean_dec(x_751);
lean_inc(x_3);
lean_inc(x_752);
x_754 = l_Lean_Elab_Term_tryPostponeIfMVar(x_752, x_3, x_753);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_764; 
x_755 = lean_ctor_get(x_754, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_756 = x_754;
} else {
 lean_dec_ref(x_754);
 x_756 = lean_box(0);
}
x_764 = l_Lean_Expr_getAppFn___main(x_752);
if (lean_obj_tag(x_764) == 4)
{
lean_object* x_765; lean_object* x_766; 
lean_dec(x_752);
lean_dec(x_3);
x_765 = lean_ctor_get(x_764, 0);
lean_inc(x_765);
lean_dec(x_764);
if (lean_is_scalar(x_756)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_756;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_755);
return x_766;
}
else
{
lean_object* x_767; 
lean_dec(x_764);
lean_dec(x_756);
x_767 = lean_box(0);
x_757 = x_767;
goto block_763;
}
block_763:
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_757);
x_758 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_758, 0, x_752);
x_759 = l_Lean_indentExpr(x_758);
x_760 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_761 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_761, 0, x_760);
lean_ctor_set(x_761, 1, x_759);
x_762 = l_Lean_Elab_Term_throwError___rarg(x_761, x_3, x_755);
return x_762;
}
}
else
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_752);
lean_dec(x_3);
x_768 = lean_ctor_get(x_754, 0);
lean_inc(x_768);
x_769 = lean_ctor_get(x_754, 1);
lean_inc(x_769);
if (lean_is_exclusive(x_754)) {
 lean_ctor_release(x_754, 0);
 lean_ctor_release(x_754, 1);
 x_770 = x_754;
} else {
 lean_dec_ref(x_754);
 x_770 = lean_box(0);
}
if (lean_is_scalar(x_770)) {
 x_771 = lean_alloc_ctor(1, 2, 0);
} else {
 x_771 = x_770;
}
lean_ctor_set(x_771, 0, x_768);
lean_ctor_set(x_771, 1, x_769);
return x_771;
}
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; 
lean_dec(x_3);
x_772 = lean_ctor_get(x_751, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_751, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_774 = x_751;
} else {
 lean_dec_ref(x_751);
 x_774 = lean_box(0);
}
if (lean_is_scalar(x_774)) {
 x_775 = lean_alloc_ctor(1, 2, 0);
} else {
 x_775 = x_774;
}
lean_ctor_set(x_775, 0, x_772);
lean_ctor_set(x_775, 1, x_773);
return x_775;
}
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; 
lean_dec(x_3);
x_776 = lean_ctor_get(x_748, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_748, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_778 = x_748;
} else {
 lean_dec_ref(x_748);
 x_778 = lean_box(0);
}
if (lean_is_scalar(x_778)) {
 x_779 = lean_alloc_ctor(1, 2, 0);
} else {
 x_779 = x_778;
}
lean_ctor_set(x_779, 0, x_776);
lean_ctor_set(x_779, 1, x_777);
return x_779;
}
}
else
{
lean_object* x_780; 
lean_dec(x_2);
x_780 = lean_box(0);
x_637 = x_780;
goto block_643;
}
}
case 4:
{
lean_object* x_781; lean_object* x_782; 
lean_dec(x_69);
lean_dec(x_3);
lean_dec(x_2);
x_781 = lean_ctor_get(x_644, 0);
lean_inc(x_781);
lean_dec(x_644);
x_782 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_636);
return x_782;
}
case 5:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_783; lean_object* x_784; 
lean_dec(x_69);
x_783 = lean_ctor_get(x_2, 1);
lean_inc(x_783);
lean_dec(x_2);
lean_inc(x_3);
x_784 = l_Lean_Elab_Term_inferType(x_783, x_3, x_636);
if (lean_obj_tag(x_784) == 0)
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_785 = lean_ctor_get(x_784, 0);
lean_inc(x_785);
x_786 = lean_ctor_get(x_784, 1);
lean_inc(x_786);
lean_dec(x_784);
lean_inc(x_3);
x_787 = l_Lean_Elab_Term_whnf(x_785, x_3, x_786);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
lean_inc(x_3);
lean_inc(x_788);
x_790 = l_Lean_Elab_Term_tryPostponeIfMVar(x_788, x_3, x_789);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_800; 
x_791 = lean_ctor_get(x_790, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_792 = x_790;
} else {
 lean_dec_ref(x_790);
 x_792 = lean_box(0);
}
x_800 = l_Lean_Expr_getAppFn___main(x_788);
if (lean_obj_tag(x_800) == 4)
{
lean_object* x_801; lean_object* x_802; 
lean_dec(x_788);
lean_dec(x_3);
x_801 = lean_ctor_get(x_800, 0);
lean_inc(x_801);
lean_dec(x_800);
if (lean_is_scalar(x_792)) {
 x_802 = lean_alloc_ctor(0, 2, 0);
} else {
 x_802 = x_792;
}
lean_ctor_set(x_802, 0, x_801);
lean_ctor_set(x_802, 1, x_791);
return x_802;
}
else
{
lean_object* x_803; 
lean_dec(x_800);
lean_dec(x_792);
x_803 = lean_box(0);
x_793 = x_803;
goto block_799;
}
block_799:
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_793);
x_794 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_794, 0, x_788);
x_795 = l_Lean_indentExpr(x_794);
x_796 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_797 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_795);
x_798 = l_Lean_Elab_Term_throwError___rarg(x_797, x_3, x_791);
return x_798;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_788);
lean_dec(x_3);
x_804 = lean_ctor_get(x_790, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_790, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_806 = x_790;
} else {
 lean_dec_ref(x_790);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_804);
lean_ctor_set(x_807, 1, x_805);
return x_807;
}
}
else
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_3);
x_808 = lean_ctor_get(x_787, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_787, 1);
lean_inc(x_809);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_810 = x_787;
} else {
 lean_dec_ref(x_787);
 x_810 = lean_box(0);
}
if (lean_is_scalar(x_810)) {
 x_811 = lean_alloc_ctor(1, 2, 0);
} else {
 x_811 = x_810;
}
lean_ctor_set(x_811, 0, x_808);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
lean_dec(x_3);
x_812 = lean_ctor_get(x_784, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_784, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_784)) {
 lean_ctor_release(x_784, 0);
 lean_ctor_release(x_784, 1);
 x_814 = x_784;
} else {
 lean_dec_ref(x_784);
 x_814 = lean_box(0);
}
if (lean_is_scalar(x_814)) {
 x_815 = lean_alloc_ctor(1, 2, 0);
} else {
 x_815 = x_814;
}
lean_ctor_set(x_815, 0, x_812);
lean_ctor_set(x_815, 1, x_813);
return x_815;
}
}
else
{
lean_object* x_816; 
lean_dec(x_2);
x_816 = lean_box(0);
x_637 = x_816;
goto block_643;
}
}
case 6:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_817; lean_object* x_818; 
lean_dec(x_69);
x_817 = lean_ctor_get(x_2, 1);
lean_inc(x_817);
lean_dec(x_2);
lean_inc(x_3);
x_818 = l_Lean_Elab_Term_inferType(x_817, x_3, x_636);
if (lean_obj_tag(x_818) == 0)
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_819 = lean_ctor_get(x_818, 0);
lean_inc(x_819);
x_820 = lean_ctor_get(x_818, 1);
lean_inc(x_820);
lean_dec(x_818);
lean_inc(x_3);
x_821 = l_Lean_Elab_Term_whnf(x_819, x_3, x_820);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
lean_inc(x_3);
lean_inc(x_822);
x_824 = l_Lean_Elab_Term_tryPostponeIfMVar(x_822, x_3, x_823);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_834; 
x_825 = lean_ctor_get(x_824, 1);
lean_inc(x_825);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_826 = x_824;
} else {
 lean_dec_ref(x_824);
 x_826 = lean_box(0);
}
x_834 = l_Lean_Expr_getAppFn___main(x_822);
if (lean_obj_tag(x_834) == 4)
{
lean_object* x_835; lean_object* x_836; 
lean_dec(x_822);
lean_dec(x_3);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
lean_dec(x_834);
if (lean_is_scalar(x_826)) {
 x_836 = lean_alloc_ctor(0, 2, 0);
} else {
 x_836 = x_826;
}
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_825);
return x_836;
}
else
{
lean_object* x_837; 
lean_dec(x_834);
lean_dec(x_826);
x_837 = lean_box(0);
x_827 = x_837;
goto block_833;
}
block_833:
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
lean_dec(x_827);
x_828 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_828, 0, x_822);
x_829 = l_Lean_indentExpr(x_828);
x_830 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_831 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_829);
x_832 = l_Lean_Elab_Term_throwError___rarg(x_831, x_3, x_825);
return x_832;
}
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
lean_dec(x_822);
lean_dec(x_3);
x_838 = lean_ctor_get(x_824, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_824, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_840 = x_824;
} else {
 lean_dec_ref(x_824);
 x_840 = lean_box(0);
}
if (lean_is_scalar(x_840)) {
 x_841 = lean_alloc_ctor(1, 2, 0);
} else {
 x_841 = x_840;
}
lean_ctor_set(x_841, 0, x_838);
lean_ctor_set(x_841, 1, x_839);
return x_841;
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
lean_dec(x_3);
x_842 = lean_ctor_get(x_821, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_821, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_844 = x_821;
} else {
 lean_dec_ref(x_821);
 x_844 = lean_box(0);
}
if (lean_is_scalar(x_844)) {
 x_845 = lean_alloc_ctor(1, 2, 0);
} else {
 x_845 = x_844;
}
lean_ctor_set(x_845, 0, x_842);
lean_ctor_set(x_845, 1, x_843);
return x_845;
}
}
else
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
lean_dec(x_3);
x_846 = lean_ctor_get(x_818, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_818, 1);
lean_inc(x_847);
if (lean_is_exclusive(x_818)) {
 lean_ctor_release(x_818, 0);
 lean_ctor_release(x_818, 1);
 x_848 = x_818;
} else {
 lean_dec_ref(x_818);
 x_848 = lean_box(0);
}
if (lean_is_scalar(x_848)) {
 x_849 = lean_alloc_ctor(1, 2, 0);
} else {
 x_849 = x_848;
}
lean_ctor_set(x_849, 0, x_846);
lean_ctor_set(x_849, 1, x_847);
return x_849;
}
}
else
{
lean_object* x_850; 
lean_dec(x_2);
x_850 = lean_box(0);
x_637 = x_850;
goto block_643;
}
}
case 7:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_851; lean_object* x_852; 
lean_dec(x_69);
x_851 = lean_ctor_get(x_2, 1);
lean_inc(x_851);
lean_dec(x_2);
lean_inc(x_3);
x_852 = l_Lean_Elab_Term_inferType(x_851, x_3, x_636);
if (lean_obj_tag(x_852) == 0)
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_852, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_852, 1);
lean_inc(x_854);
lean_dec(x_852);
lean_inc(x_3);
x_855 = l_Lean_Elab_Term_whnf(x_853, x_3, x_854);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
lean_inc(x_3);
lean_inc(x_856);
x_858 = l_Lean_Elab_Term_tryPostponeIfMVar(x_856, x_3, x_857);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_868; 
x_859 = lean_ctor_get(x_858, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_860 = x_858;
} else {
 lean_dec_ref(x_858);
 x_860 = lean_box(0);
}
x_868 = l_Lean_Expr_getAppFn___main(x_856);
if (lean_obj_tag(x_868) == 4)
{
lean_object* x_869; lean_object* x_870; 
lean_dec(x_856);
lean_dec(x_3);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
lean_dec(x_868);
if (lean_is_scalar(x_860)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_860;
}
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_859);
return x_870;
}
else
{
lean_object* x_871; 
lean_dec(x_868);
lean_dec(x_860);
x_871 = lean_box(0);
x_861 = x_871;
goto block_867;
}
block_867:
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; 
lean_dec(x_861);
x_862 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_862, 0, x_856);
x_863 = l_Lean_indentExpr(x_862);
x_864 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_865 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_863);
x_866 = l_Lean_Elab_Term_throwError___rarg(x_865, x_3, x_859);
return x_866;
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_856);
lean_dec(x_3);
x_872 = lean_ctor_get(x_858, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_858, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_874 = x_858;
} else {
 lean_dec_ref(x_858);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_3);
x_876 = lean_ctor_get(x_855, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_855, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_855)) {
 lean_ctor_release(x_855, 0);
 lean_ctor_release(x_855, 1);
 x_878 = x_855;
} else {
 lean_dec_ref(x_855);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_3);
x_880 = lean_ctor_get(x_852, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_852, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_852)) {
 lean_ctor_release(x_852, 0);
 lean_ctor_release(x_852, 1);
 x_882 = x_852;
} else {
 lean_dec_ref(x_852);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
else
{
lean_object* x_884; 
lean_dec(x_2);
x_884 = lean_box(0);
x_637 = x_884;
goto block_643;
}
}
case 8:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_885; lean_object* x_886; 
lean_dec(x_69);
x_885 = lean_ctor_get(x_2, 1);
lean_inc(x_885);
lean_dec(x_2);
lean_inc(x_3);
x_886 = l_Lean_Elab_Term_inferType(x_885, x_3, x_636);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
lean_inc(x_3);
x_889 = l_Lean_Elab_Term_whnf(x_887, x_3, x_888);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
lean_inc(x_3);
lean_inc(x_890);
x_892 = l_Lean_Elab_Term_tryPostponeIfMVar(x_890, x_3, x_891);
if (lean_obj_tag(x_892) == 0)
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_902; 
x_893 = lean_ctor_get(x_892, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 x_894 = x_892;
} else {
 lean_dec_ref(x_892);
 x_894 = lean_box(0);
}
x_902 = l_Lean_Expr_getAppFn___main(x_890);
if (lean_obj_tag(x_902) == 4)
{
lean_object* x_903; lean_object* x_904; 
lean_dec(x_890);
lean_dec(x_3);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
lean_dec(x_902);
if (lean_is_scalar(x_894)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_894;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_893);
return x_904;
}
else
{
lean_object* x_905; 
lean_dec(x_902);
lean_dec(x_894);
x_905 = lean_box(0);
x_895 = x_905;
goto block_901;
}
block_901:
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_895);
x_896 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_896, 0, x_890);
x_897 = l_Lean_indentExpr(x_896);
x_898 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_899 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_897);
x_900 = l_Lean_Elab_Term_throwError___rarg(x_899, x_3, x_893);
return x_900;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_890);
lean_dec(x_3);
x_906 = lean_ctor_get(x_892, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_892, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_892)) {
 lean_ctor_release(x_892, 0);
 lean_ctor_release(x_892, 1);
 x_908 = x_892;
} else {
 lean_dec_ref(x_892);
 x_908 = lean_box(0);
}
if (lean_is_scalar(x_908)) {
 x_909 = lean_alloc_ctor(1, 2, 0);
} else {
 x_909 = x_908;
}
lean_ctor_set(x_909, 0, x_906);
lean_ctor_set(x_909, 1, x_907);
return x_909;
}
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_3);
x_910 = lean_ctor_get(x_889, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_889, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_912 = x_889;
} else {
 lean_dec_ref(x_889);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_3);
x_914 = lean_ctor_get(x_886, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_886, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_916 = x_886;
} else {
 lean_dec_ref(x_886);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_914);
lean_ctor_set(x_917, 1, x_915);
return x_917;
}
}
else
{
lean_object* x_918; 
lean_dec(x_2);
x_918 = lean_box(0);
x_637 = x_918;
goto block_643;
}
}
case 9:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_919; lean_object* x_920; 
lean_dec(x_69);
x_919 = lean_ctor_get(x_2, 1);
lean_inc(x_919);
lean_dec(x_2);
lean_inc(x_3);
x_920 = l_Lean_Elab_Term_inferType(x_919, x_3, x_636);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
lean_inc(x_3);
x_923 = l_Lean_Elab_Term_whnf(x_921, x_3, x_922);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
lean_dec(x_923);
lean_inc(x_3);
lean_inc(x_924);
x_926 = l_Lean_Elab_Term_tryPostponeIfMVar(x_924, x_3, x_925);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_936; 
x_927 = lean_ctor_get(x_926, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_928 = x_926;
} else {
 lean_dec_ref(x_926);
 x_928 = lean_box(0);
}
x_936 = l_Lean_Expr_getAppFn___main(x_924);
if (lean_obj_tag(x_936) == 4)
{
lean_object* x_937; lean_object* x_938; 
lean_dec(x_924);
lean_dec(x_3);
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
lean_dec(x_936);
if (lean_is_scalar(x_928)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_928;
}
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_927);
return x_938;
}
else
{
lean_object* x_939; 
lean_dec(x_936);
lean_dec(x_928);
x_939 = lean_box(0);
x_929 = x_939;
goto block_935;
}
block_935:
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_929);
x_930 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_930, 0, x_924);
x_931 = l_Lean_indentExpr(x_930);
x_932 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_933 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_933, 0, x_932);
lean_ctor_set(x_933, 1, x_931);
x_934 = l_Lean_Elab_Term_throwError___rarg(x_933, x_3, x_927);
return x_934;
}
}
else
{
lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; 
lean_dec(x_924);
lean_dec(x_3);
x_940 = lean_ctor_get(x_926, 0);
lean_inc(x_940);
x_941 = lean_ctor_get(x_926, 1);
lean_inc(x_941);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_942 = x_926;
} else {
 lean_dec_ref(x_926);
 x_942 = lean_box(0);
}
if (lean_is_scalar(x_942)) {
 x_943 = lean_alloc_ctor(1, 2, 0);
} else {
 x_943 = x_942;
}
lean_ctor_set(x_943, 0, x_940);
lean_ctor_set(x_943, 1, x_941);
return x_943;
}
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
lean_dec(x_3);
x_944 = lean_ctor_get(x_923, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_923, 1);
lean_inc(x_945);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_946 = x_923;
} else {
 lean_dec_ref(x_923);
 x_946 = lean_box(0);
}
if (lean_is_scalar(x_946)) {
 x_947 = lean_alloc_ctor(1, 2, 0);
} else {
 x_947 = x_946;
}
lean_ctor_set(x_947, 0, x_944);
lean_ctor_set(x_947, 1, x_945);
return x_947;
}
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
lean_dec(x_3);
x_948 = lean_ctor_get(x_920, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_920, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_950 = x_920;
} else {
 lean_dec_ref(x_920);
 x_950 = lean_box(0);
}
if (lean_is_scalar(x_950)) {
 x_951 = lean_alloc_ctor(1, 2, 0);
} else {
 x_951 = x_950;
}
lean_ctor_set(x_951, 0, x_948);
lean_ctor_set(x_951, 1, x_949);
return x_951;
}
}
else
{
lean_object* x_952; 
lean_dec(x_2);
x_952 = lean_box(0);
x_637 = x_952;
goto block_643;
}
}
case 10:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_953; lean_object* x_954; 
lean_dec(x_69);
x_953 = lean_ctor_get(x_2, 1);
lean_inc(x_953);
lean_dec(x_2);
lean_inc(x_3);
x_954 = l_Lean_Elab_Term_inferType(x_953, x_3, x_636);
if (lean_obj_tag(x_954) == 0)
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
x_955 = lean_ctor_get(x_954, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_954, 1);
lean_inc(x_956);
lean_dec(x_954);
lean_inc(x_3);
x_957 = l_Lean_Elab_Term_whnf(x_955, x_3, x_956);
if (lean_obj_tag(x_957) == 0)
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
lean_dec(x_957);
lean_inc(x_3);
lean_inc(x_958);
x_960 = l_Lean_Elab_Term_tryPostponeIfMVar(x_958, x_3, x_959);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_970; 
x_961 = lean_ctor_get(x_960, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_962 = x_960;
} else {
 lean_dec_ref(x_960);
 x_962 = lean_box(0);
}
x_970 = l_Lean_Expr_getAppFn___main(x_958);
if (lean_obj_tag(x_970) == 4)
{
lean_object* x_971; lean_object* x_972; 
lean_dec(x_958);
lean_dec(x_3);
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
lean_dec(x_970);
if (lean_is_scalar(x_962)) {
 x_972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_972 = x_962;
}
lean_ctor_set(x_972, 0, x_971);
lean_ctor_set(x_972, 1, x_961);
return x_972;
}
else
{
lean_object* x_973; 
lean_dec(x_970);
lean_dec(x_962);
x_973 = lean_box(0);
x_963 = x_973;
goto block_969;
}
block_969:
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_963);
x_964 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_964, 0, x_958);
x_965 = l_Lean_indentExpr(x_964);
x_966 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_967 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_967, 0, x_966);
lean_ctor_set(x_967, 1, x_965);
x_968 = l_Lean_Elab_Term_throwError___rarg(x_967, x_3, x_961);
return x_968;
}
}
else
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_958);
lean_dec(x_3);
x_974 = lean_ctor_get(x_960, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_960, 1);
lean_inc(x_975);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_976 = x_960;
} else {
 lean_dec_ref(x_960);
 x_976 = lean_box(0);
}
if (lean_is_scalar(x_976)) {
 x_977 = lean_alloc_ctor(1, 2, 0);
} else {
 x_977 = x_976;
}
lean_ctor_set(x_977, 0, x_974);
lean_ctor_set(x_977, 1, x_975);
return x_977;
}
}
else
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_3);
x_978 = lean_ctor_get(x_957, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_957, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_980 = x_957;
} else {
 lean_dec_ref(x_957);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_980)) {
 x_981 = lean_alloc_ctor(1, 2, 0);
} else {
 x_981 = x_980;
}
lean_ctor_set(x_981, 0, x_978);
lean_ctor_set(x_981, 1, x_979);
return x_981;
}
}
else
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
lean_dec(x_3);
x_982 = lean_ctor_get(x_954, 0);
lean_inc(x_982);
x_983 = lean_ctor_get(x_954, 1);
lean_inc(x_983);
if (lean_is_exclusive(x_954)) {
 lean_ctor_release(x_954, 0);
 lean_ctor_release(x_954, 1);
 x_984 = x_954;
} else {
 lean_dec_ref(x_954);
 x_984 = lean_box(0);
}
if (lean_is_scalar(x_984)) {
 x_985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_985 = x_984;
}
lean_ctor_set(x_985, 0, x_982);
lean_ctor_set(x_985, 1, x_983);
return x_985;
}
}
else
{
lean_object* x_986; 
lean_dec(x_2);
x_986 = lean_box(0);
x_637 = x_986;
goto block_643;
}
}
case 11:
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_987; lean_object* x_988; 
lean_dec(x_69);
x_987 = lean_ctor_get(x_2, 1);
lean_inc(x_987);
lean_dec(x_2);
lean_inc(x_3);
x_988 = l_Lean_Elab_Term_inferType(x_987, x_3, x_636);
if (lean_obj_tag(x_988) == 0)
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
x_989 = lean_ctor_get(x_988, 0);
lean_inc(x_989);
x_990 = lean_ctor_get(x_988, 1);
lean_inc(x_990);
lean_dec(x_988);
lean_inc(x_3);
x_991 = l_Lean_Elab_Term_whnf(x_989, x_3, x_990);
if (lean_obj_tag(x_991) == 0)
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_991, 0);
lean_inc(x_992);
x_993 = lean_ctor_get(x_991, 1);
lean_inc(x_993);
lean_dec(x_991);
lean_inc(x_3);
lean_inc(x_992);
x_994 = l_Lean_Elab_Term_tryPostponeIfMVar(x_992, x_3, x_993);
if (lean_obj_tag(x_994) == 0)
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_1004; 
x_995 = lean_ctor_get(x_994, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_996 = x_994;
} else {
 lean_dec_ref(x_994);
 x_996 = lean_box(0);
}
x_1004 = l_Lean_Expr_getAppFn___main(x_992);
if (lean_obj_tag(x_1004) == 4)
{
lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_992);
lean_dec(x_3);
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
lean_dec(x_1004);
if (lean_is_scalar(x_996)) {
 x_1006 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1006 = x_996;
}
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_995);
return x_1006;
}
else
{
lean_object* x_1007; 
lean_dec(x_1004);
lean_dec(x_996);
x_1007 = lean_box(0);
x_997 = x_1007;
goto block_1003;
}
block_1003:
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
lean_dec(x_997);
x_998 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_998, 0, x_992);
x_999 = l_Lean_indentExpr(x_998);
x_1000 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_1001 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_999);
x_1002 = l_Lean_Elab_Term_throwError___rarg(x_1001, x_3, x_995);
return x_1002;
}
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_992);
lean_dec(x_3);
x_1008 = lean_ctor_get(x_994, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_994, 1);
lean_inc(x_1009);
if (lean_is_exclusive(x_994)) {
 lean_ctor_release(x_994, 0);
 lean_ctor_release(x_994, 1);
 x_1010 = x_994;
} else {
 lean_dec_ref(x_994);
 x_1010 = lean_box(0);
}
if (lean_is_scalar(x_1010)) {
 x_1011 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1011 = x_1010;
}
lean_ctor_set(x_1011, 0, x_1008);
lean_ctor_set(x_1011, 1, x_1009);
return x_1011;
}
}
else
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
lean_dec(x_3);
x_1012 = lean_ctor_get(x_991, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_991, 1);
lean_inc(x_1013);
if (lean_is_exclusive(x_991)) {
 lean_ctor_release(x_991, 0);
 lean_ctor_release(x_991, 1);
 x_1014 = x_991;
} else {
 lean_dec_ref(x_991);
 x_1014 = lean_box(0);
}
if (lean_is_scalar(x_1014)) {
 x_1015 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1015 = x_1014;
}
lean_ctor_set(x_1015, 0, x_1012);
lean_ctor_set(x_1015, 1, x_1013);
return x_1015;
}
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
lean_dec(x_3);
x_1016 = lean_ctor_get(x_988, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_988, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_988)) {
 lean_ctor_release(x_988, 0);
 lean_ctor_release(x_988, 1);
 x_1018 = x_988;
} else {
 lean_dec_ref(x_988);
 x_1018 = lean_box(0);
}
if (lean_is_scalar(x_1018)) {
 x_1019 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1019 = x_1018;
}
lean_ctor_set(x_1019, 0, x_1016);
lean_ctor_set(x_1019, 1, x_1017);
return x_1019;
}
}
else
{
lean_object* x_1020; 
lean_dec(x_2);
x_1020 = lean_box(0);
x_637 = x_1020;
goto block_643;
}
}
default: 
{
lean_dec(x_644);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_69);
x_1021 = lean_ctor_get(x_2, 1);
lean_inc(x_1021);
lean_dec(x_2);
lean_inc(x_3);
x_1022 = l_Lean_Elab_Term_inferType(x_1021, x_3, x_636);
if (lean_obj_tag(x_1022) == 0)
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
x_1024 = lean_ctor_get(x_1022, 1);
lean_inc(x_1024);
lean_dec(x_1022);
lean_inc(x_3);
x_1025 = l_Lean_Elab_Term_whnf(x_1023, x_3, x_1024);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
lean_inc(x_3);
lean_inc(x_1026);
x_1028 = l_Lean_Elab_Term_tryPostponeIfMVar(x_1026, x_3, x_1027);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1038; 
x_1029 = lean_ctor_get(x_1028, 1);
lean_inc(x_1029);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1030 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1030 = lean_box(0);
}
x_1038 = l_Lean_Expr_getAppFn___main(x_1026);
if (lean_obj_tag(x_1038) == 4)
{
lean_object* x_1039; lean_object* x_1040; 
lean_dec(x_1026);
lean_dec(x_3);
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
lean_dec(x_1038);
if (lean_is_scalar(x_1030)) {
 x_1040 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1040 = x_1030;
}
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_1029);
return x_1040;
}
else
{
lean_object* x_1041; 
lean_dec(x_1038);
lean_dec(x_1030);
x_1041 = lean_box(0);
x_1031 = x_1041;
goto block_1037;
}
block_1037:
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_1031);
x_1032 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1032, 0, x_1026);
x_1033 = l_Lean_indentExpr(x_1032);
x_1034 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_1035 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_1033);
x_1036 = l_Lean_Elab_Term_throwError___rarg(x_1035, x_3, x_1029);
return x_1036;
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; 
lean_dec(x_1026);
lean_dec(x_3);
x_1042 = lean_ctor_get(x_1028, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1028, 1);
lean_inc(x_1043);
if (lean_is_exclusive(x_1028)) {
 lean_ctor_release(x_1028, 0);
 lean_ctor_release(x_1028, 1);
 x_1044 = x_1028;
} else {
 lean_dec_ref(x_1028);
 x_1044 = lean_box(0);
}
if (lean_is_scalar(x_1044)) {
 x_1045 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1045 = x_1044;
}
lean_ctor_set(x_1045, 0, x_1042);
lean_ctor_set(x_1045, 1, x_1043);
return x_1045;
}
}
else
{
lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; 
lean_dec(x_3);
x_1046 = lean_ctor_get(x_1025, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1025, 1);
lean_inc(x_1047);
if (lean_is_exclusive(x_1025)) {
 lean_ctor_release(x_1025, 0);
 lean_ctor_release(x_1025, 1);
 x_1048 = x_1025;
} else {
 lean_dec_ref(x_1025);
 x_1048 = lean_box(0);
}
if (lean_is_scalar(x_1048)) {
 x_1049 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1049 = x_1048;
}
lean_ctor_set(x_1049, 0, x_1046);
lean_ctor_set(x_1049, 1, x_1047);
return x_1049;
}
}
else
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_3);
x_1050 = lean_ctor_get(x_1022, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1022, 1);
lean_inc(x_1051);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1052 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1052 = lean_box(0);
}
if (lean_is_scalar(x_1052)) {
 x_1053 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1053 = x_1052;
}
lean_ctor_set(x_1053, 0, x_1050);
lean_ctor_set(x_1053, 1, x_1051);
return x_1053;
}
}
else
{
lean_object* x_1054; 
lean_dec(x_2);
x_1054 = lean_box(0);
x_637 = x_1054;
goto block_643;
}
}
}
block_643:
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_637);
x_638 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_638, 0, x_69);
x_639 = l_Lean_indentExpr(x_638);
x_640 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_641 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_639);
x_642 = l_Lean_Elab_Term_throwError___rarg(x_641, x_3, x_636);
return x_642;
}
}
}
else
{
uint8_t x_1055; 
lean_dec(x_69);
lean_dec(x_3);
lean_dec(x_2);
x_1055 = !lean_is_exclusive(x_70);
if (x_1055 == 0)
{
return x_70;
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1056 = lean_ctor_get(x_70, 0);
x_1057 = lean_ctor_get(x_70, 1);
lean_inc(x_1057);
lean_inc(x_1056);
lean_dec(x_70);
x_1058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1058, 0, x_1056);
lean_ctor_set(x_1058, 1, x_1057);
return x_1058;
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
uint8_t x_1059; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1059 = !lean_is_exclusive(x_5);
if (x_1059 == 0)
{
return x_5;
}
else
{
lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; 
x_1060 = lean_ctor_get(x_5, 0);
x_1061 = lean_ctor_get(x_5, 1);
lean_inc(x_1061);
lean_inc(x_1060);
lean_dec(x_5);
x_1062 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1062, 0, x_1060);
lean_ctor_set(x_1062, 1, x_1061);
return x_1062;
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
x_36 = l_Lean_Core_getConstInfo___closed__5;
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
x_15 = l_Lean_Core_getConstInfo___closed__5;
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Syntax_getArg(x_32, x_33);
lean_dec(x_32);
lean_inc(x_9);
x_35 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_34, x_9);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
lean_dec(x_15);
x_44 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_9);
x_45 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_6, x_9, x_44, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_5);
lean_inc(x_4);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_5);
lean_ctor_set(x_48, 3, x_46);
x_49 = lean_apply_3(x_7, x_48, x_11, x_47);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_9);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_5);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_4);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_56, 2, x_52);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_10);
lean_ctor_set(x_49, 0, x_57);
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
lean_inc(x_4);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_9);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_5);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_4);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_60);
lean_ctor_set(x_64, 3, x_63);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_10);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_59);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_49);
if (x_67 == 0)
{
return x_49;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_49, 0);
x_69 = lean_ctor_get(x_49, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_49);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_43);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_45);
if (x_71 == 0)
{
return x_45;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_45, 0);
x_73 = lean_ctor_get(x_45, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_45);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_ctor_get(x_14, 0);
lean_inc(x_75);
lean_dec(x_14);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_10);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_12);
return x_77;
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Syntax_getArg(x_39, x_40);
lean_dec(x_39);
lean_inc(x_15);
x_42 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_41, x_15);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_5);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_15);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_box(0);
lean_inc(x_5);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
x_8 = x_17;
x_9 = x_49;
goto _start;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
lean_inc(x_51);
lean_dec(x_20);
x_52 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_10);
lean_inc(x_15);
lean_inc(x_3);
x_53 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_15, x_52, x_10, x_11);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_6);
lean_inc(x_5);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_51);
lean_ctor_set(x_56, 2, x_6);
lean_ctor_set(x_56, 3, x_54);
lean_inc(x_10);
x_57 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_56, x_10, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_58);
lean_inc(x_5);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_5);
lean_ctor_set(x_61, 1, x_15);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_box(0);
lean_inc(x_5);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_5);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_9);
x_8 = x_17;
x_9 = x_66;
x_11 = x_59;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_57);
if (x_68 == 0)
{
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
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
lean_dec(x_51);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_53);
if (x_72 == 0)
{
return x_53;
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
return x_75;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_15);
x_76 = lean_ctor_get(x_19, 0);
lean_inc(x_76);
lean_dec(x_19);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_9);
x_8 = x_17;
x_9 = x_77;
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
lean_inc(x_3);
x_21 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_19, x_20, x_2, x_3, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_17, 2);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_23, x_24, x_3, x_22);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_3);
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
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_42, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_42, 2);
lean_inc(x_67);
lean_dec(x_42);
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
lean_inc(x_4);
x_70 = l_Lean_Elab_Term_elabTermEnsuringType(x_68, x_69, x_4, x_43);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = l_Lean_mkApp(x_30, x_72);
x_74 = lean_expr_instantiate1(x_67, x_72);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_8, 3, x_75);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_74);
lean_ctor_set(x_2, 0, x_73);
lean_ctor_set(x_70, 0, x_2);
x_10 = x_70;
goto block_18;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_70, 0);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_70);
lean_inc(x_76);
x_78 = l_Lean_mkApp(x_30, x_76);
x_79 = lean_expr_instantiate1(x_67, x_76);
lean_dec(x_67);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_8, 3, x_80);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_79);
lean_ctor_set(x_2, 0, x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_77);
x_10 = x_81;
goto block_18;
}
}
else
{
uint8_t x_82; 
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
x_82 = !lean_is_exclusive(x_70);
if (x_82 == 0)
{
x_10 = x_70;
goto block_18;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_70, 0);
x_84 = lean_ctor_get(x_70, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_70);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_10 = x_85;
goto block_18;
}
}
}
case 1:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_free_object(x_2);
x_86 = lean_ctor_get(x_42, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_42, 2);
lean_inc(x_87);
lean_dec(x_42);
x_88 = !lean_is_exclusive(x_37);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_37, 0);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_86);
lean_inc(x_4);
lean_inc(x_90);
x_91 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_89, x_90, x_4, x_43);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_4);
x_97 = l_Lean_Elab_Term_ensureHasType(x_90, x_95, x_4, x_93);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_97, 0);
lean_ctor_set(x_37, 0, x_96);
lean_inc(x_99);
x_100 = l_Lean_mkApp(x_30, x_99);
x_101 = lean_expr_instantiate1(x_87, x_99);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_8, 3, x_102);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_92, 1, x_3);
lean_ctor_set(x_92, 0, x_101);
lean_ctor_set(x_24, 1, x_92);
lean_ctor_set(x_24, 0, x_100);
lean_ctor_set(x_97, 0, x_24);
x_10 = x_97;
goto block_18;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_97, 0);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_97);
lean_ctor_set(x_37, 0, x_96);
lean_inc(x_103);
x_105 = l_Lean_mkApp(x_30, x_103);
x_106 = lean_expr_instantiate1(x_87, x_103);
lean_dec(x_87);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_8, 3, x_107);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_92, 1, x_3);
lean_ctor_set(x_92, 0, x_106);
lean_ctor_set(x_24, 1, x_92);
lean_ctor_set(x_24, 0, x_105);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_24);
lean_ctor_set(x_108, 1, x_104);
x_10 = x_108;
goto block_18;
}
}
else
{
uint8_t x_109; 
lean_free_object(x_92);
lean_dec(x_96);
lean_free_object(x_37);
lean_dec(x_87);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_109 = !lean_is_exclusive(x_97);
if (x_109 == 0)
{
x_10 = x_97;
goto block_18;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_97, 0);
x_111 = lean_ctor_get(x_97, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_97);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_10 = x_112;
goto block_18;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_92, 0);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_92);
lean_inc(x_4);
x_115 = l_Lean_Elab_Term_ensureHasType(x_90, x_113, x_4, x_93);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
lean_ctor_set(x_37, 0, x_114);
lean_inc(x_116);
x_119 = l_Lean_mkApp(x_30, x_116);
x_120 = lean_expr_instantiate1(x_87, x_116);
lean_dec(x_87);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_8, 3, x_121);
lean_ctor_set(x_3, 1, x_35);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_3);
lean_ctor_set(x_24, 1, x_122);
lean_ctor_set(x_24, 0, x_119);
if (lean_is_scalar(x_118)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_118;
}
lean_ctor_set(x_123, 0, x_24);
lean_ctor_set(x_123, 1, x_117);
x_10 = x_123;
goto block_18;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_114);
lean_free_object(x_37);
lean_dec(x_87);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
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
x_10 = x_127;
goto block_18;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_90);
lean_free_object(x_37);
lean_dec(x_87);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_128 = !lean_is_exclusive(x_91);
if (x_128 == 0)
{
x_10 = x_91;
goto block_18;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_91, 0);
x_130 = lean_ctor_get(x_91, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_91);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_10 = x_131;
goto block_18;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_37, 0);
lean_inc(x_132);
lean_dec(x_37);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_86);
lean_inc(x_4);
lean_inc(x_133);
x_134 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_132, x_133, x_4, x_43);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_ctor_get(x_135, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_135, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_139 = x_135;
} else {
 lean_dec_ref(x_135);
 x_139 = lean_box(0);
}
lean_inc(x_4);
x_140 = l_Lean_Elab_Term_ensureHasType(x_133, x_137, x_4, x_136);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_138);
lean_inc(x_141);
x_145 = l_Lean_mkApp(x_30, x_141);
x_146 = lean_expr_instantiate1(x_87, x_141);
lean_dec(x_87);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_8, 3, x_147);
lean_ctor_set(x_8, 2, x_144);
lean_ctor_set(x_3, 1, x_35);
if (lean_is_scalar(x_139)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_139;
}
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_3);
lean_ctor_set(x_24, 1, x_148);
lean_ctor_set(x_24, 0, x_145);
if (lean_is_scalar(x_143)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_143;
}
lean_ctor_set(x_149, 0, x_24);
lean_ctor_set(x_149, 1, x_142);
x_10 = x_149;
goto block_18;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_87);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_150 = lean_ctor_get(x_140, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_140, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_152 = x_140;
} else {
 lean_dec_ref(x_140);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
x_10 = x_153;
goto block_18;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_133);
lean_dec(x_87);
lean_free_object(x_8);
lean_dec(x_36);
lean_free_object(x_24);
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_154 = lean_ctor_get(x_134, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_134, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_156 = x_134;
} else {
 lean_dec_ref(x_134);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
x_10 = x_157;
goto block_18;
}
}
}
default: 
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_158 = lean_ctor_get(x_42, 1);
lean_inc(x_158);
x_159 = lean_ctor_get(x_42, 2);
lean_inc(x_159);
lean_dec(x_42);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_158);
x_161 = lean_ctor_get(x_4, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_4, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_4, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_4, 3);
lean_inc(x_164);
x_165 = lean_ctor_get(x_4, 4);
lean_inc(x_165);
x_166 = lean_ctor_get(x_4, 5);
lean_inc(x_166);
x_167 = lean_ctor_get(x_4, 6);
lean_inc(x_167);
x_168 = lean_ctor_get(x_4, 7);
lean_inc(x_168);
x_169 = lean_ctor_get(x_4, 8);
lean_inc(x_169);
x_170 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_171 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_172 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_173 = lean_ctor_get(x_4, 9);
lean_inc(x_173);
x_174 = l_Lean_Elab_replaceRef(x_36, x_173);
lean_dec(x_173);
x_175 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_175, 0, x_161);
lean_ctor_set(x_175, 1, x_162);
lean_ctor_set(x_175, 2, x_163);
lean_ctor_set(x_175, 3, x_164);
lean_ctor_set(x_175, 4, x_165);
lean_ctor_set(x_175, 5, x_166);
lean_ctor_set(x_175, 6, x_167);
lean_ctor_set(x_175, 7, x_168);
lean_ctor_set(x_175, 8, x_169);
lean_ctor_set(x_175, 9, x_174);
lean_ctor_set_uint8(x_175, sizeof(void*)*10, x_170);
lean_ctor_set_uint8(x_175, sizeof(void*)*10 + 1, x_171);
lean_ctor_set_uint8(x_175, sizeof(void*)*10 + 2, x_172);
x_176 = 0;
x_177 = lean_box(0);
x_178 = l_Lean_Elab_Term_mkFreshExprMVar(x_160, x_176, x_177, x_175, x_43);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_178, 0);
x_181 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_180);
lean_inc(x_181);
x_182 = l_Lean_mkApp(x_30, x_181);
x_183 = lean_expr_instantiate1(x_159, x_181);
lean_dec(x_159);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_8, 3, x_184);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_183);
lean_ctor_set(x_2, 0, x_182);
lean_ctor_set(x_178, 0, x_2);
x_10 = x_178;
goto block_18;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_178, 0);
x_186 = lean_ctor_get(x_178, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_178);
x_187 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_185);
lean_inc(x_187);
x_188 = l_Lean_mkApp(x_30, x_187);
x_189 = lean_expr_instantiate1(x_159, x_187);
lean_dec(x_159);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_8, 3, x_190);
lean_ctor_set(x_3, 1, x_35);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_189);
lean_ctor_set(x_2, 0, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_2);
lean_ctor_set(x_191, 1, x_186);
x_10 = x_191;
goto block_18;
}
}
}
}
else
{
lean_object* x_192; 
lean_free_object(x_8);
lean_dec(x_37);
lean_free_object(x_24);
lean_dec(x_35);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_192 = lean_box(0);
x_44 = x_192;
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
uint8_t x_193; 
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
x_193 = !lean_is_exclusive(x_41);
if (x_193 == 0)
{
x_10 = x_41;
goto block_18;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_41, 0);
x_195 = lean_ctor_get(x_41, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_41);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_10 = x_196;
goto block_18;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_24, 0);
x_198 = lean_ctor_get(x_24, 1);
x_199 = lean_ctor_get(x_8, 0);
x_200 = lean_ctor_get(x_8, 2);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_8);
x_201 = lean_ctor_get(x_27, 1);
lean_inc(x_201);
lean_dec(x_27);
lean_inc(x_4);
x_202 = l_Lean_Elab_Term_whnfForall(x_197, x_4, x_5);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
if (lean_obj_tag(x_203) == 7)
{
lean_dec(x_201);
switch (lean_obj_tag(x_200)) {
case 0:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_203, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_203, 2);
lean_inc(x_228);
lean_dec(x_203);
x_229 = lean_ctor_get(x_200, 0);
lean_inc(x_229);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_227);
lean_inc(x_4);
x_231 = l_Lean_Elab_Term_elabTermEnsuringType(x_229, x_230, x_4, x_204);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
lean_inc(x_232);
x_235 = l_Lean_mkApp(x_30, x_232);
x_236 = lean_expr_instantiate1(x_228, x_232);
lean_dec(x_228);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_232);
x_238 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_238, 0, x_199);
lean_ctor_set(x_238, 1, x_25);
lean_ctor_set(x_238, 2, x_200);
lean_ctor_set(x_238, 3, x_237);
lean_ctor_set(x_3, 1, x_198);
lean_ctor_set(x_3, 0, x_238);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_236);
lean_ctor_set(x_2, 0, x_235);
if (lean_is_scalar(x_234)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_234;
}
lean_ctor_set(x_239, 0, x_2);
lean_ctor_set(x_239, 1, x_233);
x_10 = x_239;
goto block_18;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_228);
lean_dec(x_200);
lean_dec(x_199);
lean_free_object(x_24);
lean_dec(x_198);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_240 = lean_ctor_get(x_231, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_231, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_242 = x_231;
} else {
 lean_dec_ref(x_231);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
x_10 = x_243;
goto block_18;
}
}
case 1:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_free_object(x_2);
x_244 = lean_ctor_get(x_203, 1);
lean_inc(x_244);
x_245 = lean_ctor_get(x_203, 2);
lean_inc(x_245);
lean_dec(x_203);
x_246 = lean_ctor_get(x_200, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_247 = x_200;
} else {
 lean_dec_ref(x_200);
 x_247 = lean_box(0);
}
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_244);
lean_inc(x_4);
lean_inc(x_248);
x_249 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_246, x_248, x_4, x_204);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_254 = x_250;
} else {
 lean_dec_ref(x_250);
 x_254 = lean_box(0);
}
lean_inc(x_4);
x_255 = l_Lean_Elab_Term_ensureHasType(x_248, x_252, x_4, x_251);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_258 = x_255;
} else {
 lean_dec_ref(x_255);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_259 = lean_alloc_ctor(1, 1, 0);
} else {
 x_259 = x_247;
}
lean_ctor_set(x_259, 0, x_253);
lean_inc(x_256);
x_260 = l_Lean_mkApp(x_30, x_256);
x_261 = lean_expr_instantiate1(x_245, x_256);
lean_dec(x_245);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_256);
x_263 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_263, 0, x_199);
lean_ctor_set(x_263, 1, x_25);
lean_ctor_set(x_263, 2, x_259);
lean_ctor_set(x_263, 3, x_262);
lean_ctor_set(x_3, 1, x_198);
lean_ctor_set(x_3, 0, x_263);
if (lean_is_scalar(x_254)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_254;
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_3);
lean_ctor_set(x_24, 1, x_264);
lean_ctor_set(x_24, 0, x_260);
if (lean_is_scalar(x_258)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_258;
}
lean_ctor_set(x_265, 0, x_24);
lean_ctor_set(x_265, 1, x_257);
x_10 = x_265;
goto block_18;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_199);
lean_free_object(x_24);
lean_dec(x_198);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_266 = lean_ctor_get(x_255, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_255, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_268 = x_255;
} else {
 lean_dec_ref(x_255);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
x_10 = x_269;
goto block_18;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_245);
lean_dec(x_199);
lean_free_object(x_24);
lean_dec(x_198);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_270 = lean_ctor_get(x_249, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_249, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_272 = x_249;
} else {
 lean_dec_ref(x_249);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
x_10 = x_273;
goto block_18;
}
}
default: 
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; uint8_t x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_274 = lean_ctor_get(x_203, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_203, 2);
lean_inc(x_275);
lean_dec(x_203);
x_276 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_276, 0, x_274);
x_277 = lean_ctor_get(x_4, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_4, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_4, 2);
lean_inc(x_279);
x_280 = lean_ctor_get(x_4, 3);
lean_inc(x_280);
x_281 = lean_ctor_get(x_4, 4);
lean_inc(x_281);
x_282 = lean_ctor_get(x_4, 5);
lean_inc(x_282);
x_283 = lean_ctor_get(x_4, 6);
lean_inc(x_283);
x_284 = lean_ctor_get(x_4, 7);
lean_inc(x_284);
x_285 = lean_ctor_get(x_4, 8);
lean_inc(x_285);
x_286 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_287 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_288 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_289 = lean_ctor_get(x_4, 9);
lean_inc(x_289);
x_290 = l_Lean_Elab_replaceRef(x_199, x_289);
lean_dec(x_289);
x_291 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_291, 0, x_277);
lean_ctor_set(x_291, 1, x_278);
lean_ctor_set(x_291, 2, x_279);
lean_ctor_set(x_291, 3, x_280);
lean_ctor_set(x_291, 4, x_281);
lean_ctor_set(x_291, 5, x_282);
lean_ctor_set(x_291, 6, x_283);
lean_ctor_set(x_291, 7, x_284);
lean_ctor_set(x_291, 8, x_285);
lean_ctor_set(x_291, 9, x_290);
lean_ctor_set_uint8(x_291, sizeof(void*)*10, x_286);
lean_ctor_set_uint8(x_291, sizeof(void*)*10 + 1, x_287);
lean_ctor_set_uint8(x_291, sizeof(void*)*10 + 2, x_288);
x_292 = 0;
x_293 = lean_box(0);
x_294 = l_Lean_Elab_Term_mkFreshExprMVar(x_276, x_292, x_293, x_291, x_204);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_297 = x_294;
} else {
 lean_dec_ref(x_294);
 x_297 = lean_box(0);
}
x_298 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_295);
lean_inc(x_298);
x_299 = l_Lean_mkApp(x_30, x_298);
x_300 = lean_expr_instantiate1(x_275, x_298);
lean_dec(x_275);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_298);
x_302 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_302, 0, x_199);
lean_ctor_set(x_302, 1, x_25);
lean_ctor_set(x_302, 2, x_200);
lean_ctor_set(x_302, 3, x_301);
lean_ctor_set(x_3, 1, x_198);
lean_ctor_set(x_3, 0, x_302);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 0, x_300);
lean_ctor_set(x_2, 0, x_299);
if (lean_is_scalar(x_297)) {
 x_303 = lean_alloc_ctor(0, 2, 0);
} else {
 x_303 = x_297;
}
lean_ctor_set(x_303, 0, x_2);
lean_ctor_set(x_303, 1, x_296);
x_10 = x_303;
goto block_18;
}
}
}
else
{
lean_object* x_304; 
lean_dec(x_200);
lean_free_object(x_24);
lean_dec(x_198);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_304 = lean_box(0);
x_205 = x_304;
goto block_226;
}
block_226:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_205);
x_206 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_207 = l_Lean_indentExpr(x_206);
x_208 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_209 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_ctor_get(x_4, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_4, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_4, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_4, 3);
lean_inc(x_213);
x_214 = lean_ctor_get(x_4, 4);
lean_inc(x_214);
x_215 = lean_ctor_get(x_4, 5);
lean_inc(x_215);
x_216 = lean_ctor_get(x_4, 6);
lean_inc(x_216);
x_217 = lean_ctor_get(x_4, 7);
lean_inc(x_217);
x_218 = lean_ctor_get(x_4, 8);
lean_inc(x_218);
x_219 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_220 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_221 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_222 = lean_ctor_get(x_4, 9);
lean_inc(x_222);
x_223 = l_Lean_Elab_replaceRef(x_199, x_222);
lean_dec(x_222);
lean_dec(x_199);
x_224 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_224, 0, x_210);
lean_ctor_set(x_224, 1, x_211);
lean_ctor_set(x_224, 2, x_212);
lean_ctor_set(x_224, 3, x_213);
lean_ctor_set(x_224, 4, x_214);
lean_ctor_set(x_224, 5, x_215);
lean_ctor_set(x_224, 6, x_216);
lean_ctor_set(x_224, 7, x_217);
lean_ctor_set(x_224, 8, x_218);
lean_ctor_set(x_224, 9, x_223);
lean_ctor_set_uint8(x_224, sizeof(void*)*10, x_219);
lean_ctor_set_uint8(x_224, sizeof(void*)*10 + 1, x_220);
lean_ctor_set_uint8(x_224, sizeof(void*)*10 + 2, x_221);
lean_inc(x_1);
x_225 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_201, x_1, x_209, x_224, x_204);
x_10 = x_225;
goto block_18;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_201);
lean_dec(x_200);
lean_dec(x_199);
lean_free_object(x_24);
lean_dec(x_198);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_305 = lean_ctor_get(x_202, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_202, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_307 = x_202;
} else {
 lean_dec_ref(x_202);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
x_10 = x_308;
goto block_18;
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_309 = lean_ctor_get(x_24, 0);
x_310 = lean_ctor_get(x_24, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_24);
x_311 = lean_ctor_get(x_8, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_8, 2);
lean_inc(x_312);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_313 = x_8;
} else {
 lean_dec_ref(x_8);
 x_313 = lean_box(0);
}
x_314 = lean_ctor_get(x_27, 1);
lean_inc(x_314);
lean_dec(x_27);
lean_inc(x_4);
x_315 = l_Lean_Elab_Term_whnfForall(x_309, x_4, x_5);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
if (lean_obj_tag(x_316) == 7)
{
lean_dec(x_314);
switch (lean_obj_tag(x_312)) {
case 0:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_316, 1);
lean_inc(x_340);
x_341 = lean_ctor_get(x_316, 2);
lean_inc(x_341);
lean_dec(x_316);
x_342 = lean_ctor_get(x_312, 0);
lean_inc(x_342);
x_343 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_343, 0, x_340);
lean_inc(x_4);
x_344 = l_Lean_Elab_Term_elabTermEnsuringType(x_342, x_343, x_4, x_317);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_347 = x_344;
} else {
 lean_dec_ref(x_344);
 x_347 = lean_box(0);
}
lean_inc(x_345);
x_348 = l_Lean_mkApp(x_30, x_345);
x_349 = lean_expr_instantiate1(x_341, x_345);
lean_dec(x_341);
x_350 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_350, 0, x_345);
if (lean_is_scalar(x_313)) {
 x_351 = lean_alloc_ctor(0, 4, 0);
} else {
 x_351 = x_313;
}
lean_ctor_set(x_351, 0, x_311);
lean_ctor_set(x_351, 1, x_25);
lean_ctor_set(x_351, 2, x_312);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set(x_3, 1, x_310);
lean_ctor_set(x_3, 0, x_351);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_3);
lean_ctor_set(x_2, 1, x_352);
lean_ctor_set(x_2, 0, x_348);
if (lean_is_scalar(x_347)) {
 x_353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_353 = x_347;
}
lean_ctor_set(x_353, 0, x_2);
lean_ctor_set(x_353, 1, x_346);
x_10 = x_353;
goto block_18;
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_341);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_354 = lean_ctor_get(x_344, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_344, 1);
lean_inc(x_355);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_356 = x_344;
} else {
 lean_dec_ref(x_344);
 x_356 = lean_box(0);
}
if (lean_is_scalar(x_356)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_356;
}
lean_ctor_set(x_357, 0, x_354);
lean_ctor_set(x_357, 1, x_355);
x_10 = x_357;
goto block_18;
}
}
case 1:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_free_object(x_2);
x_358 = lean_ctor_get(x_316, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_316, 2);
lean_inc(x_359);
lean_dec(x_316);
x_360 = lean_ctor_get(x_312, 0);
lean_inc(x_360);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 x_361 = x_312;
} else {
 lean_dec_ref(x_312);
 x_361 = lean_box(0);
}
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_358);
lean_inc(x_4);
lean_inc(x_362);
x_363 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_360, x_362, x_4, x_317);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_368 = x_364;
} else {
 lean_dec_ref(x_364);
 x_368 = lean_box(0);
}
lean_inc(x_4);
x_369 = l_Lean_Elab_Term_ensureHasType(x_362, x_366, x_4, x_365);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_372 = x_369;
} else {
 lean_dec_ref(x_369);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_373 = lean_alloc_ctor(1, 1, 0);
} else {
 x_373 = x_361;
}
lean_ctor_set(x_373, 0, x_367);
lean_inc(x_370);
x_374 = l_Lean_mkApp(x_30, x_370);
x_375 = lean_expr_instantiate1(x_359, x_370);
lean_dec(x_359);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_370);
if (lean_is_scalar(x_313)) {
 x_377 = lean_alloc_ctor(0, 4, 0);
} else {
 x_377 = x_313;
}
lean_ctor_set(x_377, 0, x_311);
lean_ctor_set(x_377, 1, x_25);
lean_ctor_set(x_377, 2, x_373);
lean_ctor_set(x_377, 3, x_376);
lean_ctor_set(x_3, 1, x_310);
lean_ctor_set(x_3, 0, x_377);
if (lean_is_scalar(x_368)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_368;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_3);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_374);
lean_ctor_set(x_379, 1, x_378);
if (lean_is_scalar(x_372)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_372;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_371);
x_10 = x_380;
goto block_18;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_361);
lean_dec(x_359);
lean_dec(x_313);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_381 = lean_ctor_get(x_369, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_369, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_383 = x_369;
} else {
 lean_dec_ref(x_369);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
x_10 = x_384;
goto block_18;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_359);
lean_dec(x_313);
lean_dec(x_311);
lean_dec(x_310);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_385 = lean_ctor_get(x_363, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_363, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_387 = x_363;
} else {
 lean_dec_ref(x_363);
 x_387 = lean_box(0);
}
if (lean_is_scalar(x_387)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_387;
}
lean_ctor_set(x_388, 0, x_385);
lean_ctor_set(x_388, 1, x_386);
x_10 = x_388;
goto block_18;
}
}
default: 
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_389 = lean_ctor_get(x_316, 1);
lean_inc(x_389);
x_390 = lean_ctor_get(x_316, 2);
lean_inc(x_390);
lean_dec(x_316);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_389);
x_392 = lean_ctor_get(x_4, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_4, 1);
lean_inc(x_393);
x_394 = lean_ctor_get(x_4, 2);
lean_inc(x_394);
x_395 = lean_ctor_get(x_4, 3);
lean_inc(x_395);
x_396 = lean_ctor_get(x_4, 4);
lean_inc(x_396);
x_397 = lean_ctor_get(x_4, 5);
lean_inc(x_397);
x_398 = lean_ctor_get(x_4, 6);
lean_inc(x_398);
x_399 = lean_ctor_get(x_4, 7);
lean_inc(x_399);
x_400 = lean_ctor_get(x_4, 8);
lean_inc(x_400);
x_401 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_402 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_403 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_404 = lean_ctor_get(x_4, 9);
lean_inc(x_404);
x_405 = l_Lean_Elab_replaceRef(x_311, x_404);
lean_dec(x_404);
x_406 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_406, 0, x_392);
lean_ctor_set(x_406, 1, x_393);
lean_ctor_set(x_406, 2, x_394);
lean_ctor_set(x_406, 3, x_395);
lean_ctor_set(x_406, 4, x_396);
lean_ctor_set(x_406, 5, x_397);
lean_ctor_set(x_406, 6, x_398);
lean_ctor_set(x_406, 7, x_399);
lean_ctor_set(x_406, 8, x_400);
lean_ctor_set(x_406, 9, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*10, x_401);
lean_ctor_set_uint8(x_406, sizeof(void*)*10 + 1, x_402);
lean_ctor_set_uint8(x_406, sizeof(void*)*10 + 2, x_403);
x_407 = 0;
x_408 = lean_box(0);
x_409 = l_Lean_Elab_Term_mkFreshExprMVar(x_391, x_407, x_408, x_406, x_317);
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
x_413 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_410);
lean_inc(x_413);
x_414 = l_Lean_mkApp(x_30, x_413);
x_415 = lean_expr_instantiate1(x_390, x_413);
lean_dec(x_390);
x_416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_416, 0, x_413);
if (lean_is_scalar(x_313)) {
 x_417 = lean_alloc_ctor(0, 4, 0);
} else {
 x_417 = x_313;
}
lean_ctor_set(x_417, 0, x_311);
lean_ctor_set(x_417, 1, x_25);
lean_ctor_set(x_417, 2, x_312);
lean_ctor_set(x_417, 3, x_416);
lean_ctor_set(x_3, 1, x_310);
lean_ctor_set(x_3, 0, x_417);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_3);
lean_ctor_set(x_2, 1, x_418);
lean_ctor_set(x_2, 0, x_414);
if (lean_is_scalar(x_412)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_412;
}
lean_ctor_set(x_419, 0, x_2);
lean_ctor_set(x_419, 1, x_411);
x_10 = x_419;
goto block_18;
}
}
}
else
{
lean_object* x_420; 
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_310);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_420 = lean_box(0);
x_318 = x_420;
goto block_339;
}
block_339:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; uint8_t x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_318);
x_319 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_319, 0, x_316);
x_320 = l_Lean_indentExpr(x_319);
x_321 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_322 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
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
x_336 = l_Lean_Elab_replaceRef(x_311, x_335);
lean_dec(x_335);
lean_dec(x_311);
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
lean_inc(x_1);
x_338 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_314, x_1, x_322, x_337, x_317);
x_10 = x_338;
goto block_18;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_312);
lean_dec(x_311);
lean_dec(x_310);
lean_free_object(x_2);
lean_dec(x_30);
lean_dec(x_25);
lean_free_object(x_3);
x_421 = lean_ctor_get(x_315, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_315, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 lean_ctor_release(x_315, 1);
 x_423 = x_315;
} else {
 lean_dec_ref(x_315);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
x_10 = x_424;
goto block_18;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_425 = lean_ctor_get(x_2, 0);
lean_inc(x_425);
lean_dec(x_2);
x_426 = lean_ctor_get(x_24, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_24, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_428 = x_24;
} else {
 lean_dec_ref(x_24);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_8, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_8, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 lean_ctor_release(x_8, 2);
 lean_ctor_release(x_8, 3);
 x_431 = x_8;
} else {
 lean_dec_ref(x_8);
 x_431 = lean_box(0);
}
x_432 = lean_ctor_get(x_27, 1);
lean_inc(x_432);
lean_dec(x_27);
lean_inc(x_4);
x_433 = l_Lean_Elab_Term_whnfForall(x_426, x_4, x_5);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
if (lean_obj_tag(x_434) == 7)
{
lean_dec(x_432);
switch (lean_obj_tag(x_430)) {
case 0:
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_458 = lean_ctor_get(x_434, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_434, 2);
lean_inc(x_459);
lean_dec(x_434);
x_460 = lean_ctor_get(x_430, 0);
lean_inc(x_460);
x_461 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_461, 0, x_458);
lean_inc(x_4);
x_462 = l_Lean_Elab_Term_elabTermEnsuringType(x_460, x_461, x_4, x_435);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_465 = x_462;
} else {
 lean_dec_ref(x_462);
 x_465 = lean_box(0);
}
lean_inc(x_463);
x_466 = l_Lean_mkApp(x_425, x_463);
x_467 = lean_expr_instantiate1(x_459, x_463);
lean_dec(x_459);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_463);
if (lean_is_scalar(x_431)) {
 x_469 = lean_alloc_ctor(0, 4, 0);
} else {
 x_469 = x_431;
}
lean_ctor_set(x_469, 0, x_429);
lean_ctor_set(x_469, 1, x_25);
lean_ctor_set(x_469, 2, x_430);
lean_ctor_set(x_469, 3, x_468);
lean_ctor_set(x_3, 1, x_427);
lean_ctor_set(x_3, 0, x_469);
if (lean_is_scalar(x_428)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_428;
}
lean_ctor_set(x_470, 0, x_467);
lean_ctor_set(x_470, 1, x_3);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_466);
lean_ctor_set(x_471, 1, x_470);
if (lean_is_scalar(x_465)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_465;
}
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_464);
x_10 = x_472;
goto block_18;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_459);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_25);
lean_free_object(x_3);
x_473 = lean_ctor_get(x_462, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_462, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 x_475 = x_462;
} else {
 lean_dec_ref(x_462);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
x_10 = x_476;
goto block_18;
}
}
case 1:
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_477 = lean_ctor_get(x_434, 1);
lean_inc(x_477);
x_478 = lean_ctor_get(x_434, 2);
lean_inc(x_478);
lean_dec(x_434);
x_479 = lean_ctor_get(x_430, 0);
lean_inc(x_479);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_480 = x_430;
} else {
 lean_dec_ref(x_430);
 x_480 = lean_box(0);
}
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_477);
lean_inc(x_4);
lean_inc(x_481);
x_482 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_479, x_481, x_4, x_435);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_482, 1);
lean_inc(x_484);
lean_dec(x_482);
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_483, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_487 = x_483;
} else {
 lean_dec_ref(x_483);
 x_487 = lean_box(0);
}
lean_inc(x_4);
x_488 = l_Lean_Elab_Term_ensureHasType(x_481, x_485, x_4, x_484);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_491 = x_488;
} else {
 lean_dec_ref(x_488);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_492 = lean_alloc_ctor(1, 1, 0);
} else {
 x_492 = x_480;
}
lean_ctor_set(x_492, 0, x_486);
lean_inc(x_489);
x_493 = l_Lean_mkApp(x_425, x_489);
x_494 = lean_expr_instantiate1(x_478, x_489);
lean_dec(x_478);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_489);
if (lean_is_scalar(x_431)) {
 x_496 = lean_alloc_ctor(0, 4, 0);
} else {
 x_496 = x_431;
}
lean_ctor_set(x_496, 0, x_429);
lean_ctor_set(x_496, 1, x_25);
lean_ctor_set(x_496, 2, x_492);
lean_ctor_set(x_496, 3, x_495);
lean_ctor_set(x_3, 1, x_427);
lean_ctor_set(x_3, 0, x_496);
if (lean_is_scalar(x_487)) {
 x_497 = lean_alloc_ctor(0, 2, 0);
} else {
 x_497 = x_487;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_3);
if (lean_is_scalar(x_428)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_428;
}
lean_ctor_set(x_498, 0, x_493);
lean_ctor_set(x_498, 1, x_497);
if (lean_is_scalar(x_491)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_491;
}
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_490);
x_10 = x_499;
goto block_18;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_487);
lean_dec(x_486);
lean_dec(x_480);
lean_dec(x_478);
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_25);
lean_free_object(x_3);
x_500 = lean_ctor_get(x_488, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_488, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_488)) {
 lean_ctor_release(x_488, 0);
 lean_ctor_release(x_488, 1);
 x_502 = x_488;
} else {
 lean_dec_ref(x_488);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
x_10 = x_503;
goto block_18;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_478);
lean_dec(x_431);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_25);
lean_free_object(x_3);
x_504 = lean_ctor_get(x_482, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_482, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_506 = x_482;
} else {
 lean_dec_ref(x_482);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
x_10 = x_507;
goto block_18;
}
}
default: 
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; uint8_t x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_508 = lean_ctor_get(x_434, 1);
lean_inc(x_508);
x_509 = lean_ctor_get(x_434, 2);
lean_inc(x_509);
lean_dec(x_434);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_508);
x_511 = lean_ctor_get(x_4, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_4, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_4, 2);
lean_inc(x_513);
x_514 = lean_ctor_get(x_4, 3);
lean_inc(x_514);
x_515 = lean_ctor_get(x_4, 4);
lean_inc(x_515);
x_516 = lean_ctor_get(x_4, 5);
lean_inc(x_516);
x_517 = lean_ctor_get(x_4, 6);
lean_inc(x_517);
x_518 = lean_ctor_get(x_4, 7);
lean_inc(x_518);
x_519 = lean_ctor_get(x_4, 8);
lean_inc(x_519);
x_520 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_521 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_522 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_523 = lean_ctor_get(x_4, 9);
lean_inc(x_523);
x_524 = l_Lean_Elab_replaceRef(x_429, x_523);
lean_dec(x_523);
x_525 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_525, 0, x_511);
lean_ctor_set(x_525, 1, x_512);
lean_ctor_set(x_525, 2, x_513);
lean_ctor_set(x_525, 3, x_514);
lean_ctor_set(x_525, 4, x_515);
lean_ctor_set(x_525, 5, x_516);
lean_ctor_set(x_525, 6, x_517);
lean_ctor_set(x_525, 7, x_518);
lean_ctor_set(x_525, 8, x_519);
lean_ctor_set(x_525, 9, x_524);
lean_ctor_set_uint8(x_525, sizeof(void*)*10, x_520);
lean_ctor_set_uint8(x_525, sizeof(void*)*10 + 1, x_521);
lean_ctor_set_uint8(x_525, sizeof(void*)*10 + 2, x_522);
x_526 = 0;
x_527 = lean_box(0);
x_528 = l_Lean_Elab_Term_mkFreshExprMVar(x_510, x_526, x_527, x_525, x_435);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_531 = x_528;
} else {
 lean_dec_ref(x_528);
 x_531 = lean_box(0);
}
x_532 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_529);
lean_inc(x_532);
x_533 = l_Lean_mkApp(x_425, x_532);
x_534 = lean_expr_instantiate1(x_509, x_532);
lean_dec(x_509);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_532);
if (lean_is_scalar(x_431)) {
 x_536 = lean_alloc_ctor(0, 4, 0);
} else {
 x_536 = x_431;
}
lean_ctor_set(x_536, 0, x_429);
lean_ctor_set(x_536, 1, x_25);
lean_ctor_set(x_536, 2, x_430);
lean_ctor_set(x_536, 3, x_535);
lean_ctor_set(x_3, 1, x_427);
lean_ctor_set(x_3, 0, x_536);
if (lean_is_scalar(x_428)) {
 x_537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_537 = x_428;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_3);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_533);
lean_ctor_set(x_538, 1, x_537);
if (lean_is_scalar(x_531)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_531;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_530);
x_10 = x_539;
goto block_18;
}
}
}
else
{
lean_object* x_540; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_25);
lean_free_object(x_3);
x_540 = lean_box(0);
x_436 = x_540;
goto block_457;
}
block_457:
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; uint8_t x_451; uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_436);
x_437 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_437, 0, x_434);
x_438 = l_Lean_indentExpr(x_437);
x_439 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_440 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
x_441 = lean_ctor_get(x_4, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_4, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_4, 2);
lean_inc(x_443);
x_444 = lean_ctor_get(x_4, 3);
lean_inc(x_444);
x_445 = lean_ctor_get(x_4, 4);
lean_inc(x_445);
x_446 = lean_ctor_get(x_4, 5);
lean_inc(x_446);
x_447 = lean_ctor_get(x_4, 6);
lean_inc(x_447);
x_448 = lean_ctor_get(x_4, 7);
lean_inc(x_448);
x_449 = lean_ctor_get(x_4, 8);
lean_inc(x_449);
x_450 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_451 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_452 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_453 = lean_ctor_get(x_4, 9);
lean_inc(x_453);
x_454 = l_Lean_Elab_replaceRef(x_429, x_453);
lean_dec(x_453);
lean_dec(x_429);
x_455 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_455, 0, x_441);
lean_ctor_set(x_455, 1, x_442);
lean_ctor_set(x_455, 2, x_443);
lean_ctor_set(x_455, 3, x_444);
lean_ctor_set(x_455, 4, x_445);
lean_ctor_set(x_455, 5, x_446);
lean_ctor_set(x_455, 6, x_447);
lean_ctor_set(x_455, 7, x_448);
lean_ctor_set(x_455, 8, x_449);
lean_ctor_set(x_455, 9, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*10, x_450);
lean_ctor_set_uint8(x_455, sizeof(void*)*10 + 1, x_451);
lean_ctor_set_uint8(x_455, sizeof(void*)*10 + 2, x_452);
lean_inc(x_1);
x_456 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_432, x_1, x_440, x_455, x_435);
x_10 = x_456;
goto block_18;
}
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_427);
lean_dec(x_425);
lean_dec(x_25);
lean_free_object(x_3);
x_541 = lean_ctor_get(x_433, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_433, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_543 = x_433;
} else {
 lean_dec_ref(x_433);
 x_543 = lean_box(0);
}
if (lean_is_scalar(x_543)) {
 x_544 = lean_alloc_ctor(1, 2, 0);
} else {
 x_544 = x_543;
}
lean_ctor_set(x_544, 0, x_541);
lean_ctor_set(x_544, 1, x_542);
x_10 = x_544;
goto block_18;
}
}
}
else
{
lean_object* x_545; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_545 = lean_box(0);
x_19 = x_545;
goto block_23;
}
}
else
{
lean_object* x_546; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_free_object(x_3);
lean_dec(x_2);
x_546 = lean_box(0);
x_19 = x_546;
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
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_558; lean_object* x_563; lean_object* x_564; 
x_547 = lean_ctor_get(x_3, 0);
x_548 = lean_ctor_get(x_3, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_3);
x_563 = lean_ctor_get(x_2, 1);
lean_inc(x_563);
x_564 = lean_ctor_get(x_547, 1);
lean_inc(x_564);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; 
lean_dec(x_563);
lean_dec(x_2);
x_565 = lean_box(0);
x_558 = x_565;
goto block_562;
}
else
{
lean_object* x_566; 
x_566 = lean_ctor_get(x_564, 0);
lean_inc(x_566);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; 
x_567 = lean_ctor_get(x_564, 1);
lean_inc(x_567);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_568 = lean_ctor_get(x_2, 0);
lean_inc(x_568);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_569 = x_2;
} else {
 lean_dec_ref(x_2);
 x_569 = lean_box(0);
}
x_570 = lean_ctor_get(x_563, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_563, 1);
lean_inc(x_571);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 lean_ctor_release(x_563, 1);
 x_572 = x_563;
} else {
 lean_dec_ref(x_563);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_547, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_547, 2);
lean_inc(x_574);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 lean_ctor_release(x_547, 2);
 lean_ctor_release(x_547, 3);
 x_575 = x_547;
} else {
 lean_dec_ref(x_547);
 x_575 = lean_box(0);
}
x_576 = lean_ctor_get(x_566, 1);
lean_inc(x_576);
lean_dec(x_566);
lean_inc(x_4);
x_577 = l_Lean_Elab_Term_whnfForall(x_570, x_4, x_5);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
if (lean_obj_tag(x_578) == 7)
{
lean_dec(x_576);
switch (lean_obj_tag(x_574)) {
case 0:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_602 = lean_ctor_get(x_578, 1);
lean_inc(x_602);
x_603 = lean_ctor_get(x_578, 2);
lean_inc(x_603);
lean_dec(x_578);
x_604 = lean_ctor_get(x_574, 0);
lean_inc(x_604);
x_605 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_605, 0, x_602);
lean_inc(x_4);
x_606 = l_Lean_Elab_Term_elabTermEnsuringType(x_604, x_605, x_4, x_579);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_607 = lean_ctor_get(x_606, 0);
lean_inc(x_607);
x_608 = lean_ctor_get(x_606, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_609 = x_606;
} else {
 lean_dec_ref(x_606);
 x_609 = lean_box(0);
}
lean_inc(x_607);
x_610 = l_Lean_mkApp(x_568, x_607);
x_611 = lean_expr_instantiate1(x_603, x_607);
lean_dec(x_603);
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_607);
if (lean_is_scalar(x_575)) {
 x_613 = lean_alloc_ctor(0, 4, 0);
} else {
 x_613 = x_575;
}
lean_ctor_set(x_613, 0, x_573);
lean_ctor_set(x_613, 1, x_564);
lean_ctor_set(x_613, 2, x_574);
lean_ctor_set(x_613, 3, x_612);
x_614 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_571);
if (lean_is_scalar(x_572)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_572;
}
lean_ctor_set(x_615, 0, x_611);
lean_ctor_set(x_615, 1, x_614);
if (lean_is_scalar(x_569)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_569;
}
lean_ctor_set(x_616, 0, x_610);
lean_ctor_set(x_616, 1, x_615);
if (lean_is_scalar(x_609)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_609;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_608);
x_549 = x_617;
goto block_557;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_603);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_564);
x_618 = lean_ctor_get(x_606, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_606, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_620 = x_606;
} else {
 lean_dec_ref(x_606);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_619);
x_549 = x_621;
goto block_557;
}
}
case 1:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_569);
x_622 = lean_ctor_get(x_578, 1);
lean_inc(x_622);
x_623 = lean_ctor_get(x_578, 2);
lean_inc(x_623);
lean_dec(x_578);
x_624 = lean_ctor_get(x_574, 0);
lean_inc(x_624);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 x_625 = x_574;
} else {
 lean_dec_ref(x_574);
 x_625 = lean_box(0);
}
x_626 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_626, 0, x_622);
lean_inc(x_4);
lean_inc(x_626);
x_627 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_624, x_626, x_4, x_579);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
x_630 = lean_ctor_get(x_628, 0);
lean_inc(x_630);
x_631 = lean_ctor_get(x_628, 1);
lean_inc(x_631);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_632 = x_628;
} else {
 lean_dec_ref(x_628);
 x_632 = lean_box(0);
}
lean_inc(x_4);
x_633 = l_Lean_Elab_Term_ensureHasType(x_626, x_630, x_4, x_629);
if (lean_obj_tag(x_633) == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_634 = lean_ctor_get(x_633, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_633, 1);
lean_inc(x_635);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_636 = x_633;
} else {
 lean_dec_ref(x_633);
 x_636 = lean_box(0);
}
if (lean_is_scalar(x_625)) {
 x_637 = lean_alloc_ctor(1, 1, 0);
} else {
 x_637 = x_625;
}
lean_ctor_set(x_637, 0, x_631);
lean_inc(x_634);
x_638 = l_Lean_mkApp(x_568, x_634);
x_639 = lean_expr_instantiate1(x_623, x_634);
lean_dec(x_623);
x_640 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_640, 0, x_634);
if (lean_is_scalar(x_575)) {
 x_641 = lean_alloc_ctor(0, 4, 0);
} else {
 x_641 = x_575;
}
lean_ctor_set(x_641, 0, x_573);
lean_ctor_set(x_641, 1, x_564);
lean_ctor_set(x_641, 2, x_637);
lean_ctor_set(x_641, 3, x_640);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_571);
if (lean_is_scalar(x_632)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_632;
}
lean_ctor_set(x_643, 0, x_639);
lean_ctor_set(x_643, 1, x_642);
if (lean_is_scalar(x_572)) {
 x_644 = lean_alloc_ctor(0, 2, 0);
} else {
 x_644 = x_572;
}
lean_ctor_set(x_644, 0, x_638);
lean_ctor_set(x_644, 1, x_643);
if (lean_is_scalar(x_636)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_636;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_635);
x_549 = x_645;
goto block_557;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_632);
lean_dec(x_631);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_575);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_568);
lean_dec(x_564);
x_646 = lean_ctor_get(x_633, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_633, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_633)) {
 lean_ctor_release(x_633, 0);
 lean_ctor_release(x_633, 1);
 x_648 = x_633;
} else {
 lean_dec_ref(x_633);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
x_549 = x_649;
goto block_557;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_575);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_568);
lean_dec(x_564);
x_650 = lean_ctor_get(x_627, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_627, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_652 = x_627;
} else {
 lean_dec_ref(x_627);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
x_549 = x_653;
goto block_557;
}
}
default: 
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; uint8_t x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_654 = lean_ctor_get(x_578, 1);
lean_inc(x_654);
x_655 = lean_ctor_get(x_578, 2);
lean_inc(x_655);
lean_dec(x_578);
x_656 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_656, 0, x_654);
x_657 = lean_ctor_get(x_4, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_4, 1);
lean_inc(x_658);
x_659 = lean_ctor_get(x_4, 2);
lean_inc(x_659);
x_660 = lean_ctor_get(x_4, 3);
lean_inc(x_660);
x_661 = lean_ctor_get(x_4, 4);
lean_inc(x_661);
x_662 = lean_ctor_get(x_4, 5);
lean_inc(x_662);
x_663 = lean_ctor_get(x_4, 6);
lean_inc(x_663);
x_664 = lean_ctor_get(x_4, 7);
lean_inc(x_664);
x_665 = lean_ctor_get(x_4, 8);
lean_inc(x_665);
x_666 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_667 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_668 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_669 = lean_ctor_get(x_4, 9);
lean_inc(x_669);
x_670 = l_Lean_Elab_replaceRef(x_573, x_669);
lean_dec(x_669);
x_671 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_671, 0, x_657);
lean_ctor_set(x_671, 1, x_658);
lean_ctor_set(x_671, 2, x_659);
lean_ctor_set(x_671, 3, x_660);
lean_ctor_set(x_671, 4, x_661);
lean_ctor_set(x_671, 5, x_662);
lean_ctor_set(x_671, 6, x_663);
lean_ctor_set(x_671, 7, x_664);
lean_ctor_set(x_671, 8, x_665);
lean_ctor_set(x_671, 9, x_670);
lean_ctor_set_uint8(x_671, sizeof(void*)*10, x_666);
lean_ctor_set_uint8(x_671, sizeof(void*)*10 + 1, x_667);
lean_ctor_set_uint8(x_671, sizeof(void*)*10 + 2, x_668);
x_672 = 0;
x_673 = lean_box(0);
x_674 = l_Lean_Elab_Term_mkFreshExprMVar(x_656, x_672, x_673, x_671, x_579);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_677 = x_674;
} else {
 lean_dec_ref(x_674);
 x_677 = lean_box(0);
}
x_678 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_675);
lean_inc(x_678);
x_679 = l_Lean_mkApp(x_568, x_678);
x_680 = lean_expr_instantiate1(x_655, x_678);
lean_dec(x_655);
x_681 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_681, 0, x_678);
if (lean_is_scalar(x_575)) {
 x_682 = lean_alloc_ctor(0, 4, 0);
} else {
 x_682 = x_575;
}
lean_ctor_set(x_682, 0, x_573);
lean_ctor_set(x_682, 1, x_564);
lean_ctor_set(x_682, 2, x_574);
lean_ctor_set(x_682, 3, x_681);
x_683 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_571);
if (lean_is_scalar(x_572)) {
 x_684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_684 = x_572;
}
lean_ctor_set(x_684, 0, x_680);
lean_ctor_set(x_684, 1, x_683);
if (lean_is_scalar(x_569)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_569;
}
lean_ctor_set(x_685, 0, x_679);
lean_ctor_set(x_685, 1, x_684);
if (lean_is_scalar(x_677)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_677;
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_676);
x_549 = x_686;
goto block_557;
}
}
}
else
{
lean_object* x_687; 
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_564);
x_687 = lean_box(0);
x_580 = x_687;
goto block_601;
}
block_601:
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; uint8_t x_595; uint8_t x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_580);
x_581 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_581, 0, x_578);
x_582 = l_Lean_indentExpr(x_581);
x_583 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_584 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_582);
x_585 = lean_ctor_get(x_4, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_4, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_4, 2);
lean_inc(x_587);
x_588 = lean_ctor_get(x_4, 3);
lean_inc(x_588);
x_589 = lean_ctor_get(x_4, 4);
lean_inc(x_589);
x_590 = lean_ctor_get(x_4, 5);
lean_inc(x_590);
x_591 = lean_ctor_get(x_4, 6);
lean_inc(x_591);
x_592 = lean_ctor_get(x_4, 7);
lean_inc(x_592);
x_593 = lean_ctor_get(x_4, 8);
lean_inc(x_593);
x_594 = lean_ctor_get_uint8(x_4, sizeof(void*)*10);
x_595 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 1);
x_596 = lean_ctor_get_uint8(x_4, sizeof(void*)*10 + 2);
x_597 = lean_ctor_get(x_4, 9);
lean_inc(x_597);
x_598 = l_Lean_Elab_replaceRef(x_573, x_597);
lean_dec(x_597);
lean_dec(x_573);
x_599 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_599, 0, x_585);
lean_ctor_set(x_599, 1, x_586);
lean_ctor_set(x_599, 2, x_587);
lean_ctor_set(x_599, 3, x_588);
lean_ctor_set(x_599, 4, x_589);
lean_ctor_set(x_599, 5, x_590);
lean_ctor_set(x_599, 6, x_591);
lean_ctor_set(x_599, 7, x_592);
lean_ctor_set(x_599, 8, x_593);
lean_ctor_set(x_599, 9, x_598);
lean_ctor_set_uint8(x_599, sizeof(void*)*10, x_594);
lean_ctor_set_uint8(x_599, sizeof(void*)*10 + 1, x_595);
lean_ctor_set_uint8(x_599, sizeof(void*)*10 + 2, x_596);
lean_inc(x_1);
x_600 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_576, x_1, x_584, x_599, x_579);
x_549 = x_600;
goto block_557;
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec(x_569);
lean_dec(x_568);
lean_dec(x_564);
x_688 = lean_ctor_get(x_577, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_577, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_690 = x_577;
} else {
 lean_dec_ref(x_577);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(1, 2, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_688);
lean_ctor_set(x_691, 1, x_689);
x_549 = x_691;
goto block_557;
}
}
else
{
lean_object* x_692; 
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_2);
x_692 = lean_box(0);
x_558 = x_692;
goto block_562;
}
}
else
{
lean_object* x_693; 
lean_dec(x_566);
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_2);
x_693 = lean_box(0);
x_558 = x_693;
goto block_562;
}
}
block_557:
{
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_2 = x_550;
x_3 = x_548;
x_5 = x_551;
goto _start;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_548);
lean_dec(x_4);
lean_dec(x_1);
x_553 = lean_ctor_get(x_549, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_549, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_555 = x_549;
} else {
 lean_dec_ref(x_549);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
block_562:
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
lean_dec(x_558);
x_559 = lean_ctor_get(x_547, 0);
lean_inc(x_559);
lean_dec(x_547);
x_560 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_4);
x_561 = l_Lean_Elab_Term_throwErrorAt___rarg(x_559, x_560, x_4, x_5);
lean_dec(x_559);
x_549 = x_561;
goto block_557;
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
x_6 = l_Lean_Meta_mkId___closed__2;
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
x_35 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_6, x_37);
lean_dec(x_6);
x_39 = lean_nat_add(x_7, x_37);
lean_dec(x_7);
x_6 = x_38;
x_7 = x_39;
x_9 = x_36;
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
x_77 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_52);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_add(x_6, x_79);
lean_dec(x_6);
x_81 = lean_nat_add(x_7, x_79);
lean_dec(x_7);
x_6 = x_80;
x_7 = x_81;
x_9 = x_78;
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
x_128 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_106);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_unsigned_to_nat(1u);
x_131 = lean_nat_add(x_6, x_130);
lean_dec(x_6);
x_132 = lean_nat_add(x_7, x_130);
lean_dec(x_7);
x_6 = x_131;
x_7 = x_132;
x_9 = x_129;
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
x_177 = l_Lean_Elab_Term_setMCtx(x_30, x_8, x_154);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_add(x_6, x_179);
lean_dec(x_6);
x_181 = lean_nat_add(x_7, x_179);
lean_dec(x_7);
x_6 = x_180;
x_7 = x_181;
x_9 = x_178;
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
lean_object* x_7; lean_object* x_102; 
x_102 = lean_ctor_get(x_1, 2);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 1)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_2);
lean_dec(x_1);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_103, x_3, x_4, x_5, x_6);
return x_104;
}
else
{
lean_object* x_105; 
lean_dec(x_102);
x_105 = lean_box(0);
x_7 = x_105;
goto block_101;
}
block_101:
{
lean_object* x_8; 
lean_dec(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_9 = l_PUnit_Inhabited;
x_10 = l_monadInhabited___rarg(x_2, x_9);
x_11 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = l_unreachable_x21___rarg(x_11);
x_13 = lean_apply_4(x_12, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
if (lean_obj_tag(x_19) == 2)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_20);
x_21 = l_Lean_Elab_Term_isExprMVarAssigned(x_20, x_5, x_6);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
lean_dec(x_3);
x_29 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_5);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_5, 9);
x_32 = l_Lean_Elab_replaceRef(x_25, x_31);
lean_dec(x_31);
lean_dec(x_25);
lean_ctor_set(x_5, 9, x_32);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_26, x_27, x_28, x_29, x_20, x_33, x_33, x_5, x_24);
lean_dec(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_35);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
lean_ctor_set(x_34, 0, x_40);
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_dec(x_34);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_4);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
lean_dec(x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_34, 0, x_48);
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_35);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_34);
if (x_53 == 0)
{
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_34, 0);
x_55 = lean_ctor_get(x_34, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_34);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
x_59 = lean_ctor_get(x_5, 2);
x_60 = lean_ctor_get(x_5, 3);
x_61 = lean_ctor_get(x_5, 4);
x_62 = lean_ctor_get(x_5, 5);
x_63 = lean_ctor_get(x_5, 6);
x_64 = lean_ctor_get(x_5, 7);
x_65 = lean_ctor_get(x_5, 8);
x_66 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_69 = lean_ctor_get(x_5, 9);
lean_inc(x_69);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
x_70 = l_Lean_Elab_replaceRef(x_25, x_69);
lean_dec(x_69);
lean_dec(x_25);
x_71 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_58);
lean_ctor_set(x_71, 2, x_59);
lean_ctor_set(x_71, 3, x_60);
lean_ctor_set(x_71, 4, x_61);
lean_ctor_set(x_71, 5, x_62);
lean_ctor_set(x_71, 6, x_63);
lean_ctor_set(x_71, 7, x_64);
lean_ctor_set(x_71, 8, x_65);
lean_ctor_set(x_71, 9, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*10, x_66);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 1, x_67);
lean_ctor_set_uint8(x_71, sizeof(void*)*10 + 2, x_68);
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_26, x_27, x_28, x_29, x_20, x_72, x_72, x_71, x_24);
lean_dec(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_74);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_4);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_77;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_76);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_4);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_74);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_88 = x_73;
} else {
 lean_dec_ref(x_73);
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
}
else
{
uint8_t x_90; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_21);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_21, 0);
lean_dec(x_91);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_4);
lean_ctor_set(x_21, 0, x_93);
return x_21;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_21, 1);
lean_inc(x_94);
lean_dec(x_21);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_4);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_box(0);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_4);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_6);
return x_100;
}
}
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_5(x_8, lean_box(0), x_9, x_4, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_3);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1), 6, 3);
lean_closure_set(x_14, 0, x_11);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_3);
x_15 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed), 7, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_12);
lean_closure_set(x_15, 2, x_3);
x_16 = lean_apply_7(x_13, lean_box(0), lean_box(0), x_14, x_15, x_4, x_5, x_6);
return x_16;
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
x_16 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
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
x_23 = l_Lean_PrettyPrinter_Parenthesizer_maybeParenthesize___closed__1;
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
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_72 = l_Lean_Elab_Term_getEnv___rarg(x_8);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_7);
x_75 = l_Lean_isStructureLike(x_73, x_7);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_81 = l_Lean_Elab_Term_throwError___rarg(x_80, x_4, x_74);
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
x_9 = x_74;
goto block_71;
}
block_71:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_7__mkStructView(x_1, x_7, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_4, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
lean_inc(x_4);
x_16 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_15, x_4, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getOptions(x_4, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_23 = l_Lean_checkTraceOption(x_20, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_4);
x_24 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_17, x_2, x_4, x_21);
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
x_29 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_28, x_4, x_26);
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
lean_dec(x_4);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_17);
x_42 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_17);
x_43 = l_Lean_Options_empty;
x_44 = l_Lean_Format_pretty(x_42, x_43);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Elab_Term_logTrace(x_22, x_46, x_4, x_21);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_4);
x_49 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_17, x_2, x_4, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_53, x_4, x_51);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_52);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
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
lean_dec(x_4);
x_63 = !lean_is_exclusive(x_49);
if (x_63 == 0)
{
return x_49;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_49, 0);
x_65 = lean_ctor_get(x_49, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_49);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
return x_16;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
x_69 = lean_ctor_get(x_16, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_16);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
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
