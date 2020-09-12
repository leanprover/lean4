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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFields(lean_object*, lean_object*);
lean_object* l_Lean_fmt___at_Lean_Position_Lean_HasFormat___spec__1(lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
extern lean_object* l_Lean_fieldIdxKind;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_List_tail_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLitAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__7;
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__4;
lean_object* l___private_Lean_Expr_4__getAppRevArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__4;
lean_object* l___private_Lean_Expr_3__getAppArgsAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7___boxed(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Format_joinSep___main___at_Lean_Elab_Term_StructInst_formatField___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
extern lean_object* l_Lean_List_format___rarg___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__7(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__19;
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_4__liftMetaMFinalizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(size_t, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___main___boxed(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
lean_object* l_Std_HashMapImp_moveEntries___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__1;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__5;
lean_object* l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst(lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__2;
extern lean_object* l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
uint8_t l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited___closed__1;
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__5;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref(lean_object*);
lean_object* l_Lean_Elab_Term_getMVarDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_List_find_x3f___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_setFields(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__2;
lean_object* l_Std_HashMap_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__4;
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
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat___closed__1;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__1;
extern lean_object* l_Id_monad;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_List_head_x21___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__7;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_27__regTraceClasses(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__26;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__7;
lean_object* l_Lean_Elab_Term_StructInst_Source_inhabited;
lean_object* l_Lean_fmt___at_Lean_Level_LevelToFormat_toResult___main___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__1;
lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple___rarg___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__7(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Format_sbracket___closed__2;
lean_object* l___private_Lean_Elab_StructInst_13__isSimpleField_x3f___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_hasFormat(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Source_isNone___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_inhabited;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__11;
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__2;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__4;
lean_object* l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object**);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__1;
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax___boxed(lean_object*);
lean_object* l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Format_joinSep___main___at___private_Lean_Data_Trie_6__toStringAux___main___spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__1;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_isSimple(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields___boxed(lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
extern lean_object* l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
lean_object* l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_toSyntax(uint8_t, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3___boxed(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__1;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_formatEntry___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_Field_toSyntax___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth(lean_object*);
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
lean_object* l___private_Lean_Elab_StructInst_7__mkStructView(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__24;
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__1;
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__10;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_prettyPrint(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_markDefaultMissing___closed__2;
lean_object* l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__2___closed__1;
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__16;
lean_object* l_Lean_getStructureFields(lean_object*, lean_object*);
lean_object* l_Function_comp___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__1;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__3(lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault___main(lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasFormat___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__6;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
lean_object* l_Lean_Elab_Term_StructInst_findField_x3f(lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_defaultMissing_x3f(lean_object*);
lean_object* l_Lean_getPathToBaseStructure_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_StructInst_findField_x3f___lambda__1(lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
lean_object* l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__1;
lean_object* l_Lean_Elab_addMacroStack(lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_findField_x3f___main___spec__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
lean_object* l___private_Lean_Elab_StructInst_8__expandCompositeFields(lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Util_4__regTraceClasses___closed__1;
uint8_t l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5___boxed(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_fields(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___boxed(lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__5;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__18;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_structName___boxed(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__5;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__26;
lean_object* l_Lean_Elab_Term_StructInst_setStructSourceSyntax(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__4(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_mkSepStx(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
extern lean_object* l_Lean_Format_sbracket___closed__3;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1(lean_object*);
lean_object* l_Lean_mkAtomFrom(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Array_umapMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_HasRepr___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__3;
lean_object* l_List_foldl___main___at_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
extern lean_object* l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
lean_object* lean_instantiate_value_lparams(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__1;
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
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Struct_source___boxed(lean_object*);
lean_object* l_Lean_Expr_betaRev(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__2;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__4;
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__14;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_ref___boxed(lean_object*);
lean_object* l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__25;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__9(lean_object*);
lean_object* l_Lean_Elab_Term_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_tryPostponeIfMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureCtor(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_source(lean_object*);
lean_object* l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Struct_hasToString___closed__1;
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduceProjOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__6;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_PUnit_Inhabited;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__1;
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__5(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__2(lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__21;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__5;
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__17;
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
lean_object* l_List_map___main___at_Lean_Elab_Term_StructInst_formatStruct___main___spec__1___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__13;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_hasToString___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__8(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__9;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__3;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__1;
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
lean_object* l_List_map___main___at___private_Lean_Elab_StructInst_8__expandCompositeFields___spec__2(lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__1;
lean_object* l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__1;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_arrayToExpr___rarg___closed__2;
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
lean_object* l_Lean_Elab_Term_StructInst_Field_hasFormat;
extern lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_Field_inhabited___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField(lean_object*);
uint8_t l_Lean_isStructureLike(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_6__toFieldLHS___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__4;
lean_object* l_ReaderT_inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__1;
lean_object* l_Lean_Elab_Term_StructInst_Field_toSyntax(lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatStruct___main___closed__2;
lean_object* l_Lean_Elab_Term_isLocalIdent_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
lean_object* l___private_Lean_Elab_StructInst_21__getForallBody___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_FieldVal_toSyntax(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__5;
lean_object* l_Lean_findField_x3f___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___boxed(lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_components(lean_object*);
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___closed__2;
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_findSome_x3f___main___rarg(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___boxed(lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_StructInst_formatField___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__27;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
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
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_255; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_isNone(x_10);
x_255 = lean_st_ref_take(x_3, x_8);
if (x_11 == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = 0;
x_12 = x_258;
x_13 = x_256;
x_14 = x_257;
goto block_254;
}
else
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_255, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
lean_dec(x_255);
x_261 = 1;
x_12 = x_261;
x_13 = x_259;
x_14 = x_260;
goto block_254;
}
block_254:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 5);
x_17 = lean_nat_add(x_16, x_9);
lean_ctor_set(x_13, 5, x_17);
x_18 = lean_st_ref_set(x_3, x_13, x_14);
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
x_21 = lean_ctor_get(x_2, 7);
lean_dec(x_21);
lean_ctor_set(x_2, 7, x_16);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Syntax_getArg(x_10, x_22);
lean_inc(x_4);
lean_inc(x_23);
x_24 = l_Lean_Elab_Term_isLocalIdent_x3f(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_34 = l_Lean_addMacroScope(x_31, x_33, x_28);
x_35 = lean_box(0);
x_36 = l_Lean_SourceInfo_inhabited___closed__1;
x_37 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_38 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
x_39 = l_Lean_Syntax_setArg(x_10, x_22, x_38);
x_40 = l_Lean_Syntax_setArg(x_1, x_9, x_39);
x_41 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = l_Lean_addMacroScope(x_46, x_33, x_42);
x_48 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_37);
lean_ctor_set(x_48, 2, x_47);
lean_ctor_set(x_48, 3, x_35);
x_49 = l_Array_empty___closed__1;
x_50 = lean_array_push(x_49, x_48);
x_51 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_52 = lean_array_push(x_50, x_51);
x_53 = lean_array_push(x_52, x_51);
x_54 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_array_push(x_55, x_23);
x_57 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = lean_array_push(x_49, x_58);
x_60 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_63 = lean_array_push(x_62, x_61);
x_64 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_65 = lean_array_push(x_63, x_64);
x_66 = lean_array_push(x_65, x_40);
x_67 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_44, 0, x_69);
return x_44;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_70 = lean_ctor_get(x_44, 0);
x_71 = lean_ctor_get(x_44, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_44);
x_72 = l_Lean_addMacroScope(x_70, x_33, x_42);
x_73 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_73, 0, x_36);
lean_ctor_set(x_73, 1, x_37);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_35);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_73);
x_76 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_array_push(x_77, x_76);
x_79 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_80 = lean_array_push(x_78, x_79);
x_81 = lean_array_push(x_80, x_23);
x_82 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
x_84 = lean_array_push(x_74, x_83);
x_85 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_88 = lean_array_push(x_87, x_86);
x_89 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_90 = lean_array_push(x_88, x_89);
x_91 = lean_array_push(x_90, x_40);
x_92 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_71);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_2);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_24);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_24, 0);
lean_dec(x_97);
x_98 = lean_box(0);
lean_ctor_set(x_24, 0, x_98);
return x_24;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_24, 1);
lean_inc(x_99);
lean_dec(x_24);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_102 = lean_ctor_get(x_2, 0);
x_103 = lean_ctor_get(x_2, 1);
x_104 = lean_ctor_get(x_2, 2);
x_105 = lean_ctor_get(x_2, 3);
x_106 = lean_ctor_get(x_2, 4);
x_107 = lean_ctor_get(x_2, 5);
x_108 = lean_ctor_get(x_2, 6);
x_109 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_110 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_111 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_2);
x_112 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_103);
lean_ctor_set(x_112, 2, x_104);
lean_ctor_set(x_112, 3, x_105);
lean_ctor_set(x_112, 4, x_106);
lean_ctor_set(x_112, 5, x_107);
lean_ctor_set(x_112, 6, x_108);
lean_ctor_set(x_112, 7, x_16);
lean_ctor_set_uint8(x_112, sizeof(void*)*8, x_109);
lean_ctor_set_uint8(x_112, sizeof(void*)*8 + 1, x_110);
lean_ctor_set_uint8(x_112, sizeof(void*)*8 + 2, x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_Syntax_getArg(x_10, x_113);
lean_inc(x_4);
lean_inc(x_114);
x_115 = l_Lean_Elab_Term_isLocalIdent_x3f(x_114, x_112, x_3, x_4, x_5, x_6, x_7, x_19);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Elab_Term_getCurrMacroScope(x_112, x_3, x_4, x_5, x_6, x_7, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_125 = l_Lean_addMacroScope(x_122, x_124, x_119);
x_126 = lean_box(0);
x_127 = l_Lean_SourceInfo_inhabited___closed__1;
x_128 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_129 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_125);
lean_ctor_set(x_129, 3, x_126);
x_130 = l_Lean_Syntax_setArg(x_10, x_113, x_129);
x_131 = l_Lean_Syntax_setArg(x_1, x_9, x_130);
x_132 = l_Lean_Elab_Term_getCurrMacroScope(x_112, x_3, x_4, x_5, x_6, x_7, x_123);
lean_dec(x_4);
lean_dec(x_112);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = l_Lean_addMacroScope(x_136, x_124, x_133);
x_140 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_140, 0, x_127);
lean_ctor_set(x_140, 1, x_128);
lean_ctor_set(x_140, 2, x_139);
lean_ctor_set(x_140, 3, x_126);
x_141 = l_Array_empty___closed__1;
x_142 = lean_array_push(x_141, x_140);
x_143 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_144 = lean_array_push(x_142, x_143);
x_145 = lean_array_push(x_144, x_143);
x_146 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_147 = lean_array_push(x_145, x_146);
x_148 = lean_array_push(x_147, x_114);
x_149 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = lean_array_push(x_141, x_150);
x_152 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_155 = lean_array_push(x_154, x_153);
x_156 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_157 = lean_array_push(x_155, x_156);
x_158 = lean_array_push(x_157, x_131);
x_159 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_158);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
if (lean_is_scalar(x_138)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_138;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_137);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_163 = lean_ctor_get(x_115, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_164 = x_115;
} else {
 lean_dec_ref(x_115);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_167 = !lean_is_exclusive(x_18);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_18, 0);
lean_dec(x_168);
x_169 = lean_box(0);
lean_ctor_set(x_18, 0, x_169);
return x_18;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_18, 1);
lean_inc(x_170);
lean_dec(x_18);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_173 = lean_ctor_get(x_13, 0);
x_174 = lean_ctor_get(x_13, 1);
x_175 = lean_ctor_get(x_13, 2);
x_176 = lean_ctor_get(x_13, 3);
x_177 = lean_ctor_get(x_13, 4);
x_178 = lean_ctor_get(x_13, 5);
x_179 = lean_ctor_get(x_13, 6);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_13);
x_180 = lean_nat_add(x_178, x_9);
x_181 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_174);
lean_ctor_set(x_181, 2, x_175);
lean_ctor_set(x_181, 3, x_176);
lean_ctor_set(x_181, 4, x_177);
lean_ctor_set(x_181, 5, x_180);
lean_ctor_set(x_181, 6, x_179);
x_182 = lean_st_ref_set(x_3, x_181, x_14);
if (x_12 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_ctor_get(x_2, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_2, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_2, 2);
lean_inc(x_186);
x_187 = lean_ctor_get(x_2, 3);
lean_inc(x_187);
x_188 = lean_ctor_get(x_2, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_2, 5);
lean_inc(x_189);
x_190 = lean_ctor_get(x_2, 6);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_2, sizeof(void*)*8);
x_192 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 1);
x_193 = lean_ctor_get_uint8(x_2, sizeof(void*)*8 + 2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 lean_ctor_release(x_2, 7);
 x_194 = x_2;
} else {
 lean_dec_ref(x_2);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 8, 3);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_184);
lean_ctor_set(x_195, 1, x_185);
lean_ctor_set(x_195, 2, x_186);
lean_ctor_set(x_195, 3, x_187);
lean_ctor_set(x_195, 4, x_188);
lean_ctor_set(x_195, 5, x_189);
lean_ctor_set(x_195, 6, x_190);
lean_ctor_set(x_195, 7, x_178);
lean_ctor_set_uint8(x_195, sizeof(void*)*8, x_191);
lean_ctor_set_uint8(x_195, sizeof(void*)*8 + 1, x_192);
lean_ctor_set_uint8(x_195, sizeof(void*)*8 + 2, x_193);
x_196 = lean_unsigned_to_nat(0u);
x_197 = l_Lean_Syntax_getArg(x_10, x_196);
lean_inc(x_4);
lean_inc(x_197);
x_198 = l_Lean_Elab_Term_isLocalIdent_x3f(x_197, x_195, x_3, x_4, x_5, x_6, x_7, x_183);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_Elab_Term_getCurrMacroScope(x_195, x_3, x_4, x_5, x_6, x_7, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__4;
x_208 = l_Lean_addMacroScope(x_205, x_207, x_202);
x_209 = lean_box(0);
x_210 = l_Lean_SourceInfo_inhabited___closed__1;
x_211 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___closed__3;
x_212 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
lean_ctor_set(x_212, 2, x_208);
lean_ctor_set(x_212, 3, x_209);
x_213 = l_Lean_Syntax_setArg(x_10, x_196, x_212);
x_214 = l_Lean_Syntax_setArg(x_1, x_9, x_213);
x_215 = l_Lean_Elab_Term_getCurrMacroScope(x_195, x_3, x_4, x_5, x_6, x_7, x_206);
lean_dec(x_4);
lean_dec(x_195);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_Elab_Term_getMainModule___rarg(x_7, x_217);
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = l_Lean_addMacroScope(x_219, x_207, x_216);
x_223 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_223, 0, x_210);
lean_ctor_set(x_223, 1, x_211);
lean_ctor_set(x_223, 2, x_222);
lean_ctor_set(x_223, 3, x_209);
x_224 = l_Array_empty___closed__1;
x_225 = lean_array_push(x_224, x_223);
x_226 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_227 = lean_array_push(x_225, x_226);
x_228 = lean_array_push(x_227, x_226);
x_229 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_230 = lean_array_push(x_228, x_229);
x_231 = lean_array_push(x_230, x_197);
x_232 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__8;
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_231);
x_234 = lean_array_push(x_224, x_233);
x_235 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__6;
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_234);
x_237 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__4;
x_238 = lean_array_push(x_237, x_236);
x_239 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__16;
x_240 = lean_array_push(x_238, x_239);
x_241 = lean_array_push(x_240, x_214);
x_242 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__2;
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
if (lean_is_scalar(x_221)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_221;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_220);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_1);
x_246 = lean_ctor_get(x_198, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_247 = x_198;
} else {
 lean_dec_ref(x_198);
 x_247 = lean_box(0);
}
x_248 = lean_box(0);
if (lean_is_scalar(x_247)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_247;
}
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_246);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_178);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_182, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_251 = x_182;
} else {
 lean_dec_ref(x_182);
 x_251 = lean_box(0);
}
x_252 = lean_box(0);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
return x_253;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
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
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_isNone(x_10);
if (x_13 == 0)
{
lean_object* x_66; 
x_66 = lean_box(0);
x_14 = x_66;
goto block_65;
}
else
{
uint8_t x_67; 
x_67 = l_Lean_Syntax_isNone(x_12);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_box(0);
x_14 = x_68;
goto block_65;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_8);
return x_70;
}
}
block_65:
{
lean_dec(x_14);
if (x_13 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_6, 3);
x_17 = l_Lean_replaceRef(x_1, x_16);
x_18 = l_Lean_replaceRef(x_17, x_16);
lean_dec(x_17);
x_19 = l_Lean_replaceRef(x_18, x_16);
lean_dec(x_16);
lean_dec(x_18);
lean_ctor_set(x_6, 3, x_19);
x_20 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_21 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Lean_Syntax_getArg(x_10, x_23);
lean_inc(x_4);
x_25 = l_Lean_Elab_Term_isLocalIdent_x3f(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_29 = l_unreachable_x21___rarg(x_28);
x_30 = lean_apply_7(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_ctor_get(x_26, 0);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_39 = lean_ctor_get(x_6, 0);
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_6);
x_43 = l_Lean_replaceRef(x_1, x_42);
x_44 = l_Lean_replaceRef(x_43, x_42);
lean_dec(x_43);
x_45 = l_Lean_replaceRef(x_44, x_42);
lean_dec(x_42);
lean_dec(x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_41);
lean_ctor_set(x_46, 3, x_45);
x_47 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
x_48 = l___private_Lean_Elab_StructInst_2__getStructSource___closed__3;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_48, x_2, x_3, x_4, x_5, x_46, x_7, x_8);
lean_dec(x_7);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_Syntax_getArg(x_10, x_50);
lean_inc(x_4);
x_52 = l_Lean_Elab_Term_isLocalIdent_x3f(x_51, x_2, x_3, x_4, x_5, x_46, x_7, x_8);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_10);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_56 = l_unreachable_x21___rarg(x_55);
x_57 = lean_apply_7(x_56, x_2, x_3, x_4, x_5, x_46, x_7, x_54);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_ctor_set(x_61, 0, x_10);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_12);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_8);
return x_64;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_2__getStructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstArrayRef");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, can't mix field and `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid {...} notation, at most one `[..]` at a given level");
return x_1;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_15, x_16);
x_18 = l_Lean_Syntax_getKind(x_17);
x_19 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_15);
x_22 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_22;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
x_25 = l_Lean_Syntax_getKind(x_24);
x_26 = lean_name_eq(x_25, x_19);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_15);
x_27 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_30 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_15);
x_36 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_36;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_3);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = l_Lean_Syntax_getKind(x_38);
x_40 = lean_name_eq(x_39, x_19);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__5;
x_42 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8;
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_15, x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_15);
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
}
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_9, x_11, x_13, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = l_Lean_Syntax_getArg(x_22, x_13);
lean_dec(x_22);
x_24 = l_Lean_Syntax_getKind(x_23);
x_25 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_26 = lean_name_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_12);
return x_14;
}
else
{
return x_14;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_dec(x_14);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
x_29 = l_Lean_Syntax_getArg(x_28, x_13);
lean_dec(x_28);
x_30 = l_Lean_Syntax_getKind(x_29);
x_31 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_15);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_27);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_3__isModifyOp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
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
x_2 = l_System_FilePath_dirName___closed__1;
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
x_1 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__1;
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
lean_object* l___private_Lean_Elab_StructInst_4__elabModifyOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_307 = lean_ctor_get(x_9, 0);
lean_inc(x_307);
x_308 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_309 = l_Lean_checkTraceOption(x_307, x_308);
lean_dec(x_307);
if (x_309 == 0)
{
x_12 = x_11;
goto block_306;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_inc(x_2);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_2);
x_311 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__28;
x_312 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
lean_inc(x_3);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_3);
x_314 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_308, x_314, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_316 = lean_ctor_get(x_315, 1);
lean_inc(x_316);
lean_dec(x_315);
x_12 = x_316;
goto block_306;
}
block_306:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = l_Lean_Syntax_isNone(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_16 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__8;
x_23 = l_Lean_addMacroScope(x_20, x_22, x_17);
x_24 = lean_box(0);
x_25 = l_Lean_SourceInfo_inhabited___closed__1;
x_26 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__7;
x_27 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_Syntax_getArg(x_14, x_28);
lean_inc(x_29);
x_30 = l_Lean_Syntax_getKind(x_29);
x_31 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
x_32 = lean_name_eq(x_30, x_31);
lean_dec(x_30);
x_33 = l_Lean_Syntax_getArgs(x_14);
lean_dec(x_14);
x_34 = lean_array_get_size(x_33);
x_35 = l_Array_extract___rarg(x_33, x_13, x_34);
lean_dec(x_34);
lean_dec(x_33);
x_36 = l_Lean_nullKind;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_ctor_get(x_9, 0);
lean_inc(x_38);
x_39 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_40 = l_Lean_checkTraceOption(x_38, x_39);
lean_dec(x_38);
if (x_32 == 0)
{
lean_object* x_183; 
x_183 = l_Lean_Syntax_getArg(x_29, x_13);
lean_dec(x_29);
x_41 = x_183;
goto block_182;
}
else
{
x_41 = x_29;
goto block_182;
}
block_182:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_inc(x_2);
x_42 = l_Lean_Syntax_setArg(x_2, x_28, x_41);
x_43 = l_Lean_Syntax_setArg(x_42, x_13, x_37);
x_44 = l_Lean_mkOptionalNode___closed__2;
x_45 = lean_array_push(x_44, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_3, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_3, 1);
lean_inc(x_174);
x_175 = lean_array_get_size(x_174);
x_176 = lean_nat_dec_lt(x_28, x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_27);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_174);
x_47 = x_177;
goto block_172;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_178 = lean_box(0);
x_179 = lean_array_fset(x_174, x_28, x_178);
x_180 = lean_array_fset(x_179, x_28, x_27);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_173);
lean_ctor_set(x_181, 1, x_180);
x_47 = x_181;
goto block_172;
}
}
else
{
lean_dec(x_27);
lean_inc(x_3);
x_47 = x_3;
goto block_172;
}
block_172:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_1);
x_48 = l_Lean_Syntax_setArg(x_1, x_13, x_47);
x_49 = lean_unsigned_to_nat(2u);
x_50 = l_Lean_Syntax_setArg(x_48, x_49, x_46);
if (x_40 == 0)
{
x_51 = x_21;
goto block_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_inc(x_1);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_1);
x_166 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__23;
x_167 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_50);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_50);
x_169 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_39, x_169, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_51 = x_171;
goto block_164;
}
block_164:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_52 = l_Lean_Syntax_getArg(x_2, x_28);
lean_dec(x_2);
x_53 = l_Lean_Syntax_getArg(x_52, x_13);
lean_dec(x_52);
x_54 = l_Lean_Syntax_getArg(x_3, x_28);
lean_dec(x_3);
x_55 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_51);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Array_empty___closed__1;
x_62 = lean_array_push(x_61, x_54);
x_63 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__9;
x_64 = lean_array_push(x_62, x_63);
x_65 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__12;
lean_inc(x_56);
lean_inc(x_59);
x_66 = l_Lean_addMacroScope(x_59, x_65, x_56);
x_67 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__11;
x_68 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__15;
x_69 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_69, 0, x_25);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_array_push(x_64, x_69);
x_71 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_array_push(x_61, x_72);
x_74 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
lean_inc(x_56);
lean_inc(x_59);
x_75 = l_Lean_addMacroScope(x_59, x_74, x_56);
x_76 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_77 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_77, 0, x_25);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_24);
x_78 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_79 = lean_array_push(x_78, x_77);
x_80 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_81 = lean_array_push(x_79, x_80);
x_82 = lean_array_push(x_81, x_53);
x_83 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_84 = lean_array_push(x_82, x_83);
x_85 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_61, x_86);
x_88 = l_Lean_addMacroScope(x_59, x_22, x_56);
x_89 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_89, 0, x_25);
lean_ctor_set(x_89, 1, x_26);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_24);
x_90 = lean_array_push(x_61, x_89);
x_91 = l_Lean_nullKind___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__9;
x_94 = lean_array_push(x_93, x_92);
x_95 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__17;
x_96 = lean_array_push(x_94, x_95);
x_97 = lean_array_push(x_96, x_50);
x_98 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__7;
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_array_push(x_61, x_99);
x_101 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_102 = lean_array_push(x_100, x_101);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_91);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_push(x_78, x_103);
x_105 = lean_array_push(x_104, x_83);
x_106 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_108 = lean_array_push(x_87, x_107);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_91);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_array_push(x_73, x_109);
x_111 = l_Lean_mkAppStx___closed__8;
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_110);
if (x_40 == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_5);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_5, 6);
lean_inc(x_112);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_1);
lean_ctor_set(x_115, 1, x_112);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
lean_ctor_set(x_5, 6, x_116);
x_117 = 1;
x_118 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_117, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; 
x_119 = lean_ctor_get(x_5, 0);
x_120 = lean_ctor_get(x_5, 1);
x_121 = lean_ctor_get(x_5, 2);
x_122 = lean_ctor_get(x_5, 3);
x_123 = lean_ctor_get(x_5, 4);
x_124 = lean_ctor_get(x_5, 5);
x_125 = lean_ctor_get(x_5, 6);
x_126 = lean_ctor_get(x_5, 7);
x_127 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_128 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_129 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_5);
lean_inc(x_112);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_112);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_125);
x_132 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_132, 0, x_119);
lean_ctor_set(x_132, 1, x_120);
lean_ctor_set(x_132, 2, x_121);
lean_ctor_set(x_132, 3, x_122);
lean_ctor_set(x_132, 4, x_123);
lean_ctor_set(x_132, 5, x_124);
lean_ctor_set(x_132, 6, x_131);
lean_ctor_set(x_132, 7, x_126);
lean_ctor_set_uint8(x_132, sizeof(void*)*8, x_127);
lean_ctor_set_uint8(x_132, sizeof(void*)*8 + 1, x_128);
lean_ctor_set_uint8(x_132, sizeof(void*)*8 + 2, x_129);
x_133 = 1;
x_134 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_133, x_132, x_6, x_7, x_8, x_9, x_10, x_60);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_inc(x_1);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_1);
x_136 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
lean_inc(x_112);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_112);
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_39, x_139, x_5, x_6, x_7, x_8, x_9, x_10, x_60);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = !lean_is_exclusive(x_5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_5, 6);
lean_inc(x_112);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_1);
lean_ctor_set(x_144, 1, x_112);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
lean_ctor_set(x_5, 6, x_145);
x_146 = 1;
x_147 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_146, x_5, x_6, x_7, x_8, x_9, x_10, x_141);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; 
x_148 = lean_ctor_get(x_5, 0);
x_149 = lean_ctor_get(x_5, 1);
x_150 = lean_ctor_get(x_5, 2);
x_151 = lean_ctor_get(x_5, 3);
x_152 = lean_ctor_get(x_5, 4);
x_153 = lean_ctor_get(x_5, 5);
x_154 = lean_ctor_get(x_5, 6);
x_155 = lean_ctor_get(x_5, 7);
x_156 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_157 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_158 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_5);
lean_inc(x_112);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_1);
lean_ctor_set(x_159, 1, x_112);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_154);
x_161 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_161, 0, x_148);
lean_ctor_set(x_161, 1, x_149);
lean_ctor_set(x_161, 2, x_150);
lean_ctor_set(x_161, 3, x_151);
lean_ctor_set(x_161, 4, x_152);
lean_ctor_set(x_161, 5, x_153);
lean_ctor_set(x_161, 6, x_160);
lean_ctor_set(x_161, 7, x_155);
lean_ctor_set_uint8(x_161, sizeof(void*)*8, x_156);
lean_ctor_set_uint8(x_161, sizeof(void*)*8 + 1, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*8 + 2, x_158);
x_162 = 1;
x_163 = l_Lean_Elab_Term_elabTerm(x_112, x_4, x_162, x_161, x_6, x_7, x_8, x_9, x_10, x_141);
return x_163;
}
}
}
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
lean_dec(x_14);
x_184 = lean_unsigned_to_nat(3u);
x_185 = l_Lean_Syntax_getArg(x_2, x_184);
x_186 = lean_unsigned_to_nat(0u);
x_187 = l_Lean_Syntax_getArg(x_2, x_186);
lean_dec(x_2);
x_188 = l_Lean_Syntax_getArg(x_187, x_13);
lean_dec(x_187);
x_189 = l_Lean_Syntax_getArg(x_3, x_186);
lean_dec(x_3);
x_190 = l_Lean_Elab_Term_getCurrMacroScope(x_5, x_6, x_7, x_8, x_9, x_10, x_12);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Elab_Term_getMainModule___rarg(x_10, x_192);
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
x_208 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_array_push(x_196, x_209);
x_211 = l___private_Lean_Elab_App_20__elabAppLValsAux___main___closed__2;
lean_inc(x_191);
lean_inc(x_194);
x_212 = l_Lean_addMacroScope(x_194, x_211, x_191);
x_213 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__17;
x_214 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_214, 0, x_203);
lean_ctor_set(x_214, 1, x_213);
lean_ctor_set(x_214, 2, x_212);
lean_ctor_set(x_214, 3, x_202);
x_215 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_216 = lean_array_push(x_215, x_214);
x_217 = l___private_Lean_Elab_Quotation_4__getHeadInfo___elambda__3___closed__10;
x_218 = lean_array_push(x_216, x_217);
x_219 = lean_array_push(x_218, x_188);
x_220 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_221 = lean_array_push(x_219, x_220);
x_222 = l_Array_iterateMAux___main___at_Lean_Elab_Term_expandApp___spec__1___closed__2;
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
x_230 = l_Lean_nullKind___closed__2;
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
x_232 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__9;
x_233 = lean_array_push(x_232, x_231);
x_234 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__17;
x_235 = lean_array_push(x_233, x_234);
x_236 = lean_array_push(x_235, x_185);
x_237 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__7;
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = lean_array_push(x_196, x_238);
x_240 = l___private_Lean_Elab_Quotation_2__quoteSyntax___main___closed__42;
x_241 = lean_array_push(x_239, x_240);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_230);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_array_push(x_215, x_242);
x_244 = lean_array_push(x_243, x_220);
x_245 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_244);
x_247 = lean_array_push(x_224, x_246);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_230);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_array_push(x_210, x_248);
x_250 = l_Lean_mkAppStx___closed__8;
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
x_252 = lean_ctor_get(x_9, 0);
lean_inc(x_252);
x_253 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__4;
x_254 = l_Lean_checkTraceOption(x_252, x_253);
lean_dec(x_252);
if (x_254 == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_5);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_5, 6);
lean_inc(x_251);
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_1);
lean_ctor_set(x_257, 1, x_251);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
lean_ctor_set(x_5, 6, x_258);
x_259 = 1;
x_260 = l_Lean_Elab_Term_elabTerm(x_251, x_4, x_259, x_5, x_6, x_7, x_8, x_9, x_10, x_195);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_261 = lean_ctor_get(x_5, 0);
x_262 = lean_ctor_get(x_5, 1);
x_263 = lean_ctor_get(x_5, 2);
x_264 = lean_ctor_get(x_5, 3);
x_265 = lean_ctor_get(x_5, 4);
x_266 = lean_ctor_get(x_5, 5);
x_267 = lean_ctor_get(x_5, 6);
x_268 = lean_ctor_get(x_5, 7);
x_269 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_270 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_271 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_5);
lean_inc(x_251);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_1);
lean_ctor_set(x_272, 1, x_251);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_267);
x_274 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_274, 0, x_261);
lean_ctor_set(x_274, 1, x_262);
lean_ctor_set(x_274, 2, x_263);
lean_ctor_set(x_274, 3, x_264);
lean_ctor_set(x_274, 4, x_265);
lean_ctor_set(x_274, 5, x_266);
lean_ctor_set(x_274, 6, x_273);
lean_ctor_set(x_274, 7, x_268);
lean_ctor_set_uint8(x_274, sizeof(void*)*8, x_269);
lean_ctor_set_uint8(x_274, sizeof(void*)*8 + 1, x_270);
lean_ctor_set_uint8(x_274, sizeof(void*)*8 + 2, x_271);
x_275 = 1;
x_276 = l_Lean_Elab_Term_elabTerm(x_251, x_4, x_275, x_274, x_6, x_7, x_8, x_9, x_10, x_195);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_inc(x_1);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_1);
x_278 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__20;
x_279 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
lean_inc(x_251);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_251);
x_281 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_253, x_281, x_5, x_6, x_7, x_8, x_9, x_10, x_195);
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_284 = !lean_is_exclusive(x_5);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; 
x_285 = lean_ctor_get(x_5, 6);
lean_inc(x_251);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_1);
lean_ctor_set(x_286, 1, x_251);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
lean_ctor_set(x_5, 6, x_287);
x_288 = 1;
x_289 = l_Lean_Elab_Term_elabTerm(x_251, x_4, x_288, x_5, x_6, x_7, x_8, x_9, x_10, x_283);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; 
x_290 = lean_ctor_get(x_5, 0);
x_291 = lean_ctor_get(x_5, 1);
x_292 = lean_ctor_get(x_5, 2);
x_293 = lean_ctor_get(x_5, 3);
x_294 = lean_ctor_get(x_5, 4);
x_295 = lean_ctor_get(x_5, 5);
x_296 = lean_ctor_get(x_5, 6);
x_297 = lean_ctor_get(x_5, 7);
x_298 = lean_ctor_get_uint8(x_5, sizeof(void*)*8);
x_299 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 1);
x_300 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_5);
lean_inc(x_251);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_1);
lean_ctor_set(x_301, 1, x_251);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_296);
x_303 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_303, 0, x_290);
lean_ctor_set(x_303, 1, x_291);
lean_ctor_set(x_303, 2, x_292);
lean_ctor_set(x_303, 3, x_293);
lean_ctor_set(x_303, 4, x_294);
lean_ctor_set(x_303, 5, x_295);
lean_ctor_set(x_303, 6, x_302);
lean_ctor_set(x_303, 7, x_297);
lean_ctor_set_uint8(x_303, sizeof(void*)*8, x_298);
lean_ctor_set_uint8(x_303, sizeof(void*)*8 + 1, x_299);
lean_ctor_set_uint8(x_303, sizeof(void*)*8 + 2, x_300);
x_304 = 1;
x_305 = l_Lean_Elab_Term_elabTerm(x_251, x_4, x_304, x_303, x_6, x_7, x_8, x_9, x_10, x_283);
return x_305;
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
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_1);
x_10 = l_Lean_Elab_Term_tryPostponeIfNoneOrMVar(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_27 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_30 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_3);
lean_inc(x_31);
x_33 = l_Lean_Elab_Term_tryPostponeIfMVar(x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_43; 
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_43 = l_Lean_Expr_getAppFn___main(x_31);
if (lean_obj_tag(x_43) == 4)
{
lean_object* x_44; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
lean_ctor_set(x_33, 0, x_44);
return x_33;
}
else
{
lean_object* x_45; 
lean_dec(x_43);
lean_free_object(x_33);
x_45 = lean_box(0);
x_37 = x_45;
goto block_42;
}
block_42:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_37);
x_38 = l_Lean_indentExpr(x_31);
x_39 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_41;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_53; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_53 = l_Lean_Expr_getAppFn___main(x_31);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = lean_box(0);
x_47 = x_56;
goto block_52;
}
block_52:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_47);
x_48 = l_Lean_indentExpr(x_31);
x_49 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_51;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_57 = !lean_is_exclusive(x_33);
if (x_57 == 0)
{
return x_33;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_33, 0);
x_59 = lean_ctor_get(x_33, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_33);
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
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_30);
if (x_61 == 0)
{
return x_30;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_30, 0);
x_63 = lean_ctor_get(x_30, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_30);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_27);
if (x_65 == 0)
{
return x_27;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_27, 0);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_27);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_2);
x_69 = lean_box(0);
x_12 = x_69;
goto block_25;
}
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_1, 0);
lean_inc(x_70);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_70);
x_71 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_81; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
x_81 = l_Lean_Expr_getAppFn___main(x_73);
lean_dec(x_73);
switch (lean_obj_tag(x_81)) {
case 0:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_70);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_83 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_86 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
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
x_89 = l_Lean_Elab_Term_tryPostponeIfMVar(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_99; 
x_91 = lean_ctor_get(x_89, 1);
x_92 = lean_ctor_get(x_89, 0);
lean_dec(x_92);
x_99 = l_Lean_Expr_getAppFn___main(x_87);
if (lean_obj_tag(x_99) == 4)
{
lean_object* x_100; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
lean_ctor_set(x_89, 0, x_100);
return x_89;
}
else
{
lean_object* x_101; 
lean_dec(x_99);
lean_free_object(x_89);
x_101 = lean_box(0);
x_93 = x_101;
goto block_98;
}
block_98:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_93);
x_94 = l_Lean_indentExpr(x_87);
x_95 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_96 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
x_97 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_96, x_3, x_4, x_5, x_6, x_7, x_8, x_91);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_97;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_109; 
x_102 = lean_ctor_get(x_89, 1);
lean_inc(x_102);
lean_dec(x_89);
x_109 = l_Lean_Expr_getAppFn___main(x_87);
if (lean_obj_tag(x_109) == 4)
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
else
{
lean_object* x_112; 
lean_dec(x_109);
x_112 = lean_box(0);
x_103 = x_112;
goto block_108;
}
block_108:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_103);
x_104 = l_Lean_indentExpr(x_87);
x_105 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_106 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_106, x_3, x_4, x_5, x_6, x_7, x_8, x_102);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_107;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_86);
if (x_117 == 0)
{
return x_86;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_86, 0);
x_119 = lean_ctor_get(x_86, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_86);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
else
{
lean_object* x_125; 
lean_dec(x_2);
x_125 = lean_box(0);
x_75 = x_125;
goto block_80;
}
}
case 1:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_70);
x_126 = lean_ctor_get(x_2, 1);
lean_inc(x_126);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_127 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_126, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_130 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_128, x_3, x_4, x_5, x_6, x_7, x_8, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_3);
lean_inc(x_131);
x_133 = l_Lean_Elab_Term_tryPostponeIfMVar(x_131, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_143; 
x_135 = lean_ctor_get(x_133, 1);
x_136 = lean_ctor_get(x_133, 0);
lean_dec(x_136);
x_143 = l_Lean_Expr_getAppFn___main(x_131);
if (lean_obj_tag(x_143) == 4)
{
lean_object* x_144; 
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
lean_ctor_set(x_133, 0, x_144);
return x_133;
}
else
{
lean_object* x_145; 
lean_dec(x_143);
lean_free_object(x_133);
x_145 = lean_box(0);
x_137 = x_145;
goto block_142;
}
block_142:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_137);
x_138 = l_Lean_indentExpr(x_131);
x_139 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_140 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_140, x_3, x_4, x_5, x_6, x_7, x_8, x_135);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_141;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_153; 
x_146 = lean_ctor_get(x_133, 1);
lean_inc(x_146);
lean_dec(x_133);
x_153 = l_Lean_Expr_getAppFn___main(x_131);
if (lean_obj_tag(x_153) == 4)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_146);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_153);
x_156 = lean_box(0);
x_147 = x_156;
goto block_152;
}
block_152:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_147);
x_148 = l_Lean_indentExpr(x_131);
x_149 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
x_151 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_150, x_3, x_4, x_5, x_6, x_7, x_8, x_146);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_151;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_157 = !lean_is_exclusive(x_133);
if (x_157 == 0)
{
return x_133;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_133, 0);
x_159 = lean_ctor_get(x_133, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_133);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_161 = !lean_is_exclusive(x_130);
if (x_161 == 0)
{
return x_130;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_130, 0);
x_163 = lean_ctor_get(x_130, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_130);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_165 = !lean_is_exclusive(x_127);
if (x_165 == 0)
{
return x_127;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_127, 0);
x_167 = lean_ctor_get(x_127, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_127);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
lean_object* x_169; 
lean_dec(x_2);
x_169 = lean_box(0);
x_75 = x_169;
goto block_80;
}
}
case 2:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_70);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_171 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_170, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_174 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_172, x_3, x_4, x_5, x_6, x_7, x_8, x_173);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec(x_174);
lean_inc(x_3);
lean_inc(x_175);
x_177 = l_Lean_Elab_Term_tryPostponeIfMVar(x_175, x_3, x_4, x_5, x_6, x_7, x_8, x_176);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_187; 
x_179 = lean_ctor_get(x_177, 1);
x_180 = lean_ctor_get(x_177, 0);
lean_dec(x_180);
x_187 = l_Lean_Expr_getAppFn___main(x_175);
if (lean_obj_tag(x_187) == 4)
{
lean_object* x_188; 
lean_dec(x_175);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec(x_187);
lean_ctor_set(x_177, 0, x_188);
return x_177;
}
else
{
lean_object* x_189; 
lean_dec(x_187);
lean_free_object(x_177);
x_189 = lean_box(0);
x_181 = x_189;
goto block_186;
}
block_186:
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_181);
x_182 = l_Lean_indentExpr(x_175);
x_183 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_184 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_184, x_3, x_4, x_5, x_6, x_7, x_8, x_179);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_185;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_197; 
x_190 = lean_ctor_get(x_177, 1);
lean_inc(x_190);
lean_dec(x_177);
x_197 = l_Lean_Expr_getAppFn___main(x_175);
if (lean_obj_tag(x_197) == 4)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_175);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_190);
return x_199;
}
else
{
lean_object* x_200; 
lean_dec(x_197);
x_200 = lean_box(0);
x_191 = x_200;
goto block_196;
}
block_196:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_191);
x_192 = l_Lean_indentExpr(x_175);
x_193 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_194 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
x_195 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_194, x_3, x_4, x_5, x_6, x_7, x_8, x_190);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_195;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_175);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_177);
if (x_201 == 0)
{
return x_177;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_177, 0);
x_203 = lean_ctor_get(x_177, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_177);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_205 = !lean_is_exclusive(x_174);
if (x_205 == 0)
{
return x_174;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_174, 0);
x_207 = lean_ctor_get(x_174, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_174);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_209 = !lean_is_exclusive(x_171);
if (x_209 == 0)
{
return x_171;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_171, 0);
x_211 = lean_ctor_get(x_171, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_171);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
else
{
lean_object* x_213; 
lean_dec(x_2);
x_213 = lean_box(0);
x_75 = x_213;
goto block_80;
}
}
case 3:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_70);
x_214 = lean_ctor_get(x_2, 1);
lean_inc(x_214);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_215 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_214, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_218 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_216, x_3, x_4, x_5, x_6, x_7, x_8, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
lean_inc(x_3);
lean_inc(x_219);
x_221 = l_Lean_Elab_Term_tryPostponeIfMVar(x_219, x_3, x_4, x_5, x_6, x_7, x_8, x_220);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_231; 
x_223 = lean_ctor_get(x_221, 1);
x_224 = lean_ctor_get(x_221, 0);
lean_dec(x_224);
x_231 = l_Lean_Expr_getAppFn___main(x_219);
if (lean_obj_tag(x_231) == 4)
{
lean_object* x_232; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
lean_ctor_set(x_221, 0, x_232);
return x_221;
}
else
{
lean_object* x_233; 
lean_dec(x_231);
lean_free_object(x_221);
x_233 = lean_box(0);
x_225 = x_233;
goto block_230;
}
block_230:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_225);
x_226 = l_Lean_indentExpr(x_219);
x_227 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_228 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_228, x_3, x_4, x_5, x_6, x_7, x_8, x_223);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_229;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_241; 
x_234 = lean_ctor_get(x_221, 1);
lean_inc(x_234);
lean_dec(x_221);
x_241 = l_Lean_Expr_getAppFn___main(x_219);
if (lean_obj_tag(x_241) == 4)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_234);
return x_243;
}
else
{
lean_object* x_244; 
lean_dec(x_241);
x_244 = lean_box(0);
x_235 = x_244;
goto block_240;
}
block_240:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_235);
x_236 = l_Lean_indentExpr(x_219);
x_237 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_238 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_238, x_3, x_4, x_5, x_6, x_7, x_8, x_234);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_239;
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_219);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_245 = !lean_is_exclusive(x_221);
if (x_245 == 0)
{
return x_221;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_221, 0);
x_247 = lean_ctor_get(x_221, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_221);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_249 = !lean_is_exclusive(x_218);
if (x_249 == 0)
{
return x_218;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_218, 0);
x_251 = lean_ctor_get(x_218, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_218);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_215);
if (x_253 == 0)
{
return x_215;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_215, 0);
x_255 = lean_ctor_get(x_215, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_215);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; 
lean_dec(x_2);
x_257 = lean_box(0);
x_75 = x_257;
goto block_80;
}
}
case 4:
{
lean_object* x_258; 
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_258 = lean_ctor_get(x_81, 0);
lean_inc(x_258);
lean_dec(x_81);
lean_ctor_set(x_71, 0, x_258);
return x_71;
}
case 5:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_70);
x_259 = lean_ctor_get(x_2, 1);
lean_inc(x_259);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_260 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_259, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_263 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_261, x_3, x_4, x_5, x_6, x_7, x_8, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_3);
lean_inc(x_264);
x_266 = l_Lean_Elab_Term_tryPostponeIfMVar(x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_265);
if (lean_obj_tag(x_266) == 0)
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_276; 
x_268 = lean_ctor_get(x_266, 1);
x_269 = lean_ctor_get(x_266, 0);
lean_dec(x_269);
x_276 = l_Lean_Expr_getAppFn___main(x_264);
if (lean_obj_tag(x_276) == 4)
{
lean_object* x_277; 
lean_dec(x_264);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec(x_276);
lean_ctor_set(x_266, 0, x_277);
return x_266;
}
else
{
lean_object* x_278; 
lean_dec(x_276);
lean_free_object(x_266);
x_278 = lean_box(0);
x_270 = x_278;
goto block_275;
}
block_275:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_270);
x_271 = l_Lean_indentExpr(x_264);
x_272 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_273, x_3, x_4, x_5, x_6, x_7, x_8, x_268);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_274;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_286; 
x_279 = lean_ctor_get(x_266, 1);
lean_inc(x_279);
lean_dec(x_266);
x_286 = l_Lean_Expr_getAppFn___main(x_264);
if (lean_obj_tag(x_286) == 4)
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_264);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_279);
return x_288;
}
else
{
lean_object* x_289; 
lean_dec(x_286);
x_289 = lean_box(0);
x_280 = x_289;
goto block_285;
}
block_285:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_280);
x_281 = l_Lean_indentExpr(x_264);
x_282 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_283 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_281);
x_284 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_283, x_3, x_4, x_5, x_6, x_7, x_8, x_279);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_284;
}
}
}
else
{
uint8_t x_290; 
lean_dec(x_264);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_290 = !lean_is_exclusive(x_266);
if (x_290 == 0)
{
return x_266;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_266, 0);
x_292 = lean_ctor_get(x_266, 1);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_266);
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
return x_293;
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_294 = !lean_is_exclusive(x_263);
if (x_294 == 0)
{
return x_263;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_263, 0);
x_296 = lean_ctor_get(x_263, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_263);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_298 = !lean_is_exclusive(x_260);
if (x_298 == 0)
{
return x_260;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_260, 0);
x_300 = lean_ctor_get(x_260, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_260);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; 
lean_dec(x_2);
x_302 = lean_box(0);
x_75 = x_302;
goto block_80;
}
}
case 6:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_70);
x_303 = lean_ctor_get(x_2, 1);
lean_inc(x_303);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_304 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_303, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_307 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_305, x_3, x_4, x_5, x_6, x_7, x_8, x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
lean_inc(x_3);
lean_inc(x_308);
x_310 = l_Lean_Elab_Term_tryPostponeIfMVar(x_308, x_3, x_4, x_5, x_6, x_7, x_8, x_309);
if (lean_obj_tag(x_310) == 0)
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_310);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_320; 
x_312 = lean_ctor_get(x_310, 1);
x_313 = lean_ctor_get(x_310, 0);
lean_dec(x_313);
x_320 = l_Lean_Expr_getAppFn___main(x_308);
if (lean_obj_tag(x_320) == 4)
{
lean_object* x_321; 
lean_dec(x_308);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
lean_dec(x_320);
lean_ctor_set(x_310, 0, x_321);
return x_310;
}
else
{
lean_object* x_322; 
lean_dec(x_320);
lean_free_object(x_310);
x_322 = lean_box(0);
x_314 = x_322;
goto block_319;
}
block_319:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_dec(x_314);
x_315 = l_Lean_indentExpr(x_308);
x_316 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_317 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
x_318 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_317, x_3, x_4, x_5, x_6, x_7, x_8, x_312);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_318;
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_330; 
x_323 = lean_ctor_get(x_310, 1);
lean_inc(x_323);
lean_dec(x_310);
x_330 = l_Lean_Expr_getAppFn___main(x_308);
if (lean_obj_tag(x_330) == 4)
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_308);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_323);
return x_332;
}
else
{
lean_object* x_333; 
lean_dec(x_330);
x_333 = lean_box(0);
x_324 = x_333;
goto block_329;
}
block_329:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_324);
x_325 = l_Lean_indentExpr(x_308);
x_326 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_327 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_325);
x_328 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_327, x_3, x_4, x_5, x_6, x_7, x_8, x_323);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_328;
}
}
}
else
{
uint8_t x_334; 
lean_dec(x_308);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_334 = !lean_is_exclusive(x_310);
if (x_334 == 0)
{
return x_310;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_310, 0);
x_336 = lean_ctor_get(x_310, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_310);
x_337 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set(x_337, 1, x_336);
return x_337;
}
}
}
else
{
uint8_t x_338; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_338 = !lean_is_exclusive(x_307);
if (x_338 == 0)
{
return x_307;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_307, 0);
x_340 = lean_ctor_get(x_307, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_307);
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
lean_dec(x_3);
x_342 = !lean_is_exclusive(x_304);
if (x_342 == 0)
{
return x_304;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_304, 0);
x_344 = lean_ctor_get(x_304, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_304);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; 
lean_dec(x_2);
x_346 = lean_box(0);
x_75 = x_346;
goto block_80;
}
}
case 7:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_347; lean_object* x_348; 
lean_dec(x_70);
x_347 = lean_ctor_get(x_2, 1);
lean_inc(x_347);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_348 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_347, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_351 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_349, x_3, x_4, x_5, x_6, x_7, x_8, x_350);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
lean_inc(x_3);
lean_inc(x_352);
x_354 = l_Lean_Elab_Term_tryPostponeIfMVar(x_352, x_3, x_4, x_5, x_6, x_7, x_8, x_353);
if (lean_obj_tag(x_354) == 0)
{
uint8_t x_355; 
x_355 = !lean_is_exclusive(x_354);
if (x_355 == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_364; 
x_356 = lean_ctor_get(x_354, 1);
x_357 = lean_ctor_get(x_354, 0);
lean_dec(x_357);
x_364 = l_Lean_Expr_getAppFn___main(x_352);
if (lean_obj_tag(x_364) == 4)
{
lean_object* x_365; 
lean_dec(x_352);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec(x_364);
lean_ctor_set(x_354, 0, x_365);
return x_354;
}
else
{
lean_object* x_366; 
lean_dec(x_364);
lean_free_object(x_354);
x_366 = lean_box(0);
x_358 = x_366;
goto block_363;
}
block_363:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_358);
x_359 = l_Lean_indentExpr(x_352);
x_360 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_361 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
x_362 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_361, x_3, x_4, x_5, x_6, x_7, x_8, x_356);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_362;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_374; 
x_367 = lean_ctor_get(x_354, 1);
lean_inc(x_367);
lean_dec(x_354);
x_374 = l_Lean_Expr_getAppFn___main(x_352);
if (lean_obj_tag(x_374) == 4)
{
lean_object* x_375; lean_object* x_376; 
lean_dec(x_352);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec(x_374);
x_376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_367);
return x_376;
}
else
{
lean_object* x_377; 
lean_dec(x_374);
x_377 = lean_box(0);
x_368 = x_377;
goto block_373;
}
block_373:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_368);
x_369 = l_Lean_indentExpr(x_352);
x_370 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_371 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_369);
x_372 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_371, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_372;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_352);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_378 = !lean_is_exclusive(x_354);
if (x_378 == 0)
{
return x_354;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_354, 0);
x_380 = lean_ctor_get(x_354, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_354);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_382 = !lean_is_exclusive(x_351);
if (x_382 == 0)
{
return x_351;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_351, 0);
x_384 = lean_ctor_get(x_351, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_351);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_386 = !lean_is_exclusive(x_348);
if (x_386 == 0)
{
return x_348;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_348, 0);
x_388 = lean_ctor_get(x_348, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_348);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
lean_object* x_390; 
lean_dec(x_2);
x_390 = lean_box(0);
x_75 = x_390;
goto block_80;
}
}
case 8:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_391; lean_object* x_392; 
lean_dec(x_70);
x_391 = lean_ctor_get(x_2, 1);
lean_inc(x_391);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_392 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_391, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_395 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_393, x_3, x_4, x_5, x_6, x_7, x_8, x_394);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
lean_inc(x_3);
lean_inc(x_396);
x_398 = l_Lean_Elab_Term_tryPostponeIfMVar(x_396, x_3, x_4, x_5, x_6, x_7, x_8, x_397);
if (lean_obj_tag(x_398) == 0)
{
uint8_t x_399; 
x_399 = !lean_is_exclusive(x_398);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_408; 
x_400 = lean_ctor_get(x_398, 1);
x_401 = lean_ctor_get(x_398, 0);
lean_dec(x_401);
x_408 = l_Lean_Expr_getAppFn___main(x_396);
if (lean_obj_tag(x_408) == 4)
{
lean_object* x_409; 
lean_dec(x_396);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
lean_dec(x_408);
lean_ctor_set(x_398, 0, x_409);
return x_398;
}
else
{
lean_object* x_410; 
lean_dec(x_408);
lean_free_object(x_398);
x_410 = lean_box(0);
x_402 = x_410;
goto block_407;
}
block_407:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_402);
x_403 = l_Lean_indentExpr(x_396);
x_404 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_405 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
x_406 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_405, x_3, x_4, x_5, x_6, x_7, x_8, x_400);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_406;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_418; 
x_411 = lean_ctor_get(x_398, 1);
lean_inc(x_411);
lean_dec(x_398);
x_418 = l_Lean_Expr_getAppFn___main(x_396);
if (lean_obj_tag(x_418) == 4)
{
lean_object* x_419; lean_object* x_420; 
lean_dec(x_396);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
lean_dec(x_418);
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_419);
lean_ctor_set(x_420, 1, x_411);
return x_420;
}
else
{
lean_object* x_421; 
lean_dec(x_418);
x_421 = lean_box(0);
x_412 = x_421;
goto block_417;
}
block_417:
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_412);
x_413 = l_Lean_indentExpr(x_396);
x_414 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_415 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_413);
x_416 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_415, x_3, x_4, x_5, x_6, x_7, x_8, x_411);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_416;
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_396);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_422 = !lean_is_exclusive(x_398);
if (x_422 == 0)
{
return x_398;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_398, 0);
x_424 = lean_ctor_get(x_398, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_398);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_426 = !lean_is_exclusive(x_395);
if (x_426 == 0)
{
return x_395;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_395, 0);
x_428 = lean_ctor_get(x_395, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_395);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_430 = !lean_is_exclusive(x_392);
if (x_430 == 0)
{
return x_392;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_392, 0);
x_432 = lean_ctor_get(x_392, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_392);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
else
{
lean_object* x_434; 
lean_dec(x_2);
x_434 = lean_box(0);
x_75 = x_434;
goto block_80;
}
}
case 9:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_70);
x_435 = lean_ctor_get(x_2, 1);
lean_inc(x_435);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_436 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_435, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_436) == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_437 = lean_ctor_get(x_436, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_436, 1);
lean_inc(x_438);
lean_dec(x_436);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_439 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_437, x_3, x_4, x_5, x_6, x_7, x_8, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
lean_inc(x_3);
lean_inc(x_440);
x_442 = l_Lean_Elab_Term_tryPostponeIfMVar(x_440, x_3, x_4, x_5, x_6, x_7, x_8, x_441);
if (lean_obj_tag(x_442) == 0)
{
uint8_t x_443; 
x_443 = !lean_is_exclusive(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_452; 
x_444 = lean_ctor_get(x_442, 1);
x_445 = lean_ctor_get(x_442, 0);
lean_dec(x_445);
x_452 = l_Lean_Expr_getAppFn___main(x_440);
if (lean_obj_tag(x_452) == 4)
{
lean_object* x_453; 
lean_dec(x_440);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
lean_dec(x_452);
lean_ctor_set(x_442, 0, x_453);
return x_442;
}
else
{
lean_object* x_454; 
lean_dec(x_452);
lean_free_object(x_442);
x_454 = lean_box(0);
x_446 = x_454;
goto block_451;
}
block_451:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_446);
x_447 = l_Lean_indentExpr(x_440);
x_448 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_449 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_447);
x_450 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_449, x_3, x_4, x_5, x_6, x_7, x_8, x_444);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_450;
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_462; 
x_455 = lean_ctor_get(x_442, 1);
lean_inc(x_455);
lean_dec(x_442);
x_462 = l_Lean_Expr_getAppFn___main(x_440);
if (lean_obj_tag(x_462) == 4)
{
lean_object* x_463; lean_object* x_464; 
lean_dec(x_440);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec(x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_455);
return x_464;
}
else
{
lean_object* x_465; 
lean_dec(x_462);
x_465 = lean_box(0);
x_456 = x_465;
goto block_461;
}
block_461:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_456);
x_457 = l_Lean_indentExpr(x_440);
x_458 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_459 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_457);
x_460 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_459, x_3, x_4, x_5, x_6, x_7, x_8, x_455);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_460;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_440);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_466 = !lean_is_exclusive(x_442);
if (x_466 == 0)
{
return x_442;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_442, 0);
x_468 = lean_ctor_get(x_442, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_442);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_470 = !lean_is_exclusive(x_439);
if (x_470 == 0)
{
return x_439;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_439, 0);
x_472 = lean_ctor_get(x_439, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_439);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_474 = !lean_is_exclusive(x_436);
if (x_474 == 0)
{
return x_436;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_436, 0);
x_476 = lean_ctor_get(x_436, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_436);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
lean_object* x_478; 
lean_dec(x_2);
x_478 = lean_box(0);
x_75 = x_478;
goto block_80;
}
}
case 10:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_70);
x_479 = lean_ctor_get(x_2, 1);
lean_inc(x_479);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_480 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_479, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_480) == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_483 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_481, x_3, x_4, x_5, x_6, x_7, x_8, x_482);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
lean_inc(x_3);
lean_inc(x_484);
x_486 = l_Lean_Elab_Term_tryPostponeIfMVar(x_484, x_3, x_4, x_5, x_6, x_7, x_8, x_485);
if (lean_obj_tag(x_486) == 0)
{
uint8_t x_487; 
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_496; 
x_488 = lean_ctor_get(x_486, 1);
x_489 = lean_ctor_get(x_486, 0);
lean_dec(x_489);
x_496 = l_Lean_Expr_getAppFn___main(x_484);
if (lean_obj_tag(x_496) == 4)
{
lean_object* x_497; 
lean_dec(x_484);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
lean_dec(x_496);
lean_ctor_set(x_486, 0, x_497);
return x_486;
}
else
{
lean_object* x_498; 
lean_dec(x_496);
lean_free_object(x_486);
x_498 = lean_box(0);
x_490 = x_498;
goto block_495;
}
block_495:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_490);
x_491 = l_Lean_indentExpr(x_484);
x_492 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_493 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
x_494 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_493, x_3, x_4, x_5, x_6, x_7, x_8, x_488);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_494;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_506; 
x_499 = lean_ctor_get(x_486, 1);
lean_inc(x_499);
lean_dec(x_486);
x_506 = l_Lean_Expr_getAppFn___main(x_484);
if (lean_obj_tag(x_506) == 4)
{
lean_object* x_507; lean_object* x_508; 
lean_dec(x_484);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
lean_dec(x_506);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_499);
return x_508;
}
else
{
lean_object* x_509; 
lean_dec(x_506);
x_509 = lean_box(0);
x_500 = x_509;
goto block_505;
}
block_505:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_500);
x_501 = l_Lean_indentExpr(x_484);
x_502 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_503 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_501);
x_504 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_503, x_3, x_4, x_5, x_6, x_7, x_8, x_499);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_504;
}
}
}
else
{
uint8_t x_510; 
lean_dec(x_484);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_510 = !lean_is_exclusive(x_486);
if (x_510 == 0)
{
return x_486;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_486, 0);
x_512 = lean_ctor_get(x_486, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_486);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
else
{
uint8_t x_514; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_514 = !lean_is_exclusive(x_483);
if (x_514 == 0)
{
return x_483;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_483, 0);
x_516 = lean_ctor_get(x_483, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_483);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
else
{
uint8_t x_518; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_518 = !lean_is_exclusive(x_480);
if (x_518 == 0)
{
return x_480;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_480, 0);
x_520 = lean_ctor_get(x_480, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_480);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
else
{
lean_object* x_522; 
lean_dec(x_2);
x_522 = lean_box(0);
x_75 = x_522;
goto block_80;
}
}
case 11:
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_70);
x_523 = lean_ctor_get(x_2, 1);
lean_inc(x_523);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_524 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_523, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_527 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_525, x_3, x_4, x_5, x_6, x_7, x_8, x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_inc(x_3);
lean_inc(x_528);
x_530 = l_Lean_Elab_Term_tryPostponeIfMVar(x_528, x_3, x_4, x_5, x_6, x_7, x_8, x_529);
if (lean_obj_tag(x_530) == 0)
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_530);
if (x_531 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_540; 
x_532 = lean_ctor_get(x_530, 1);
x_533 = lean_ctor_get(x_530, 0);
lean_dec(x_533);
x_540 = l_Lean_Expr_getAppFn___main(x_528);
if (lean_obj_tag(x_540) == 4)
{
lean_object* x_541; 
lean_dec(x_528);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
lean_dec(x_540);
lean_ctor_set(x_530, 0, x_541);
return x_530;
}
else
{
lean_object* x_542; 
lean_dec(x_540);
lean_free_object(x_530);
x_542 = lean_box(0);
x_534 = x_542;
goto block_539;
}
block_539:
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
lean_dec(x_534);
x_535 = l_Lean_indentExpr(x_528);
x_536 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_537 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_537, 0, x_536);
lean_ctor_set(x_537, 1, x_535);
x_538 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_537, x_3, x_4, x_5, x_6, x_7, x_8, x_532);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_538;
}
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_550; 
x_543 = lean_ctor_get(x_530, 1);
lean_inc(x_543);
lean_dec(x_530);
x_550 = l_Lean_Expr_getAppFn___main(x_528);
if (lean_obj_tag(x_550) == 4)
{
lean_object* x_551; lean_object* x_552; 
lean_dec(x_528);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
lean_dec(x_550);
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_543);
return x_552;
}
else
{
lean_object* x_553; 
lean_dec(x_550);
x_553 = lean_box(0);
x_544 = x_553;
goto block_549;
}
block_549:
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_544);
x_545 = l_Lean_indentExpr(x_528);
x_546 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_547 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_545);
x_548 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_547, x_3, x_4, x_5, x_6, x_7, x_8, x_543);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_548;
}
}
}
else
{
uint8_t x_554; 
lean_dec(x_528);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_554 = !lean_is_exclusive(x_530);
if (x_554 == 0)
{
return x_530;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_530, 0);
x_556 = lean_ctor_get(x_530, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_530);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_558 = !lean_is_exclusive(x_527);
if (x_558 == 0)
{
return x_527;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_527, 0);
x_560 = lean_ctor_get(x_527, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_527);
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
lean_dec(x_3);
x_562 = !lean_is_exclusive(x_524);
if (x_562 == 0)
{
return x_524;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_524, 0);
x_564 = lean_ctor_get(x_524, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_524);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
lean_object* x_566; 
lean_dec(x_2);
x_566 = lean_box(0);
x_75 = x_566;
goto block_80;
}
}
default: 
{
lean_dec(x_81);
lean_free_object(x_71);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_70);
x_567 = lean_ctor_get(x_2, 1);
lean_inc(x_567);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_568 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_567, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_571 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_569, x_3, x_4, x_5, x_6, x_7, x_8, x_570);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
lean_inc(x_3);
lean_inc(x_572);
x_574 = l_Lean_Elab_Term_tryPostponeIfMVar(x_572, x_3, x_4, x_5, x_6, x_7, x_8, x_573);
if (lean_obj_tag(x_574) == 0)
{
uint8_t x_575; 
x_575 = !lean_is_exclusive(x_574);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_584; 
x_576 = lean_ctor_get(x_574, 1);
x_577 = lean_ctor_get(x_574, 0);
lean_dec(x_577);
x_584 = l_Lean_Expr_getAppFn___main(x_572);
if (lean_obj_tag(x_584) == 4)
{
lean_object* x_585; 
lean_dec(x_572);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
lean_dec(x_584);
lean_ctor_set(x_574, 0, x_585);
return x_574;
}
else
{
lean_object* x_586; 
lean_dec(x_584);
lean_free_object(x_574);
x_586 = lean_box(0);
x_578 = x_586;
goto block_583;
}
block_583:
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec(x_578);
x_579 = l_Lean_indentExpr(x_572);
x_580 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_581 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_579);
x_582 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_581, x_3, x_4, x_5, x_6, x_7, x_8, x_576);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_582;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_594; 
x_587 = lean_ctor_get(x_574, 1);
lean_inc(x_587);
lean_dec(x_574);
x_594 = l_Lean_Expr_getAppFn___main(x_572);
if (lean_obj_tag(x_594) == 4)
{
lean_object* x_595; lean_object* x_596; 
lean_dec(x_572);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
lean_dec(x_594);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_587);
return x_596;
}
else
{
lean_object* x_597; 
lean_dec(x_594);
x_597 = lean_box(0);
x_588 = x_597;
goto block_593;
}
block_593:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_588);
x_589 = l_Lean_indentExpr(x_572);
x_590 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_591 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
x_592 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_591, x_3, x_4, x_5, x_6, x_7, x_8, x_587);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_592;
}
}
}
else
{
uint8_t x_598; 
lean_dec(x_572);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_598 = !lean_is_exclusive(x_574);
if (x_598 == 0)
{
return x_574;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_574, 0);
x_600 = lean_ctor_get(x_574, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_574);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_599);
lean_ctor_set(x_601, 1, x_600);
return x_601;
}
}
}
else
{
uint8_t x_602; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_602 = !lean_is_exclusive(x_571);
if (x_602 == 0)
{
return x_571;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_571, 0);
x_604 = lean_ctor_get(x_571, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_571);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_606 = !lean_is_exclusive(x_568);
if (x_606 == 0)
{
return x_568;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_568, 0);
x_608 = lean_ctor_get(x_568, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_568);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
else
{
lean_object* x_610; 
lean_dec(x_2);
x_610 = lean_box(0);
x_75 = x_610;
goto block_80;
}
}
}
block_80:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_75);
x_76 = l_Lean_indentExpr(x_70);
x_77 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_78 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_74);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_79;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_619; 
x_611 = lean_ctor_get(x_71, 0);
x_612 = lean_ctor_get(x_71, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_71);
x_619 = l_Lean_Expr_getAppFn___main(x_611);
lean_dec(x_611);
switch (lean_obj_tag(x_619)) {
case 0:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_620; lean_object* x_621; 
lean_dec(x_70);
x_620 = lean_ctor_get(x_2, 1);
lean_inc(x_620);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_621 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_620, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_624 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_622, x_3, x_4, x_5, x_6, x_7, x_8, x_623);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_624, 1);
lean_inc(x_626);
lean_dec(x_624);
lean_inc(x_3);
lean_inc(x_625);
x_627 = l_Lean_Elab_Term_tryPostponeIfMVar(x_625, x_3, x_4, x_5, x_6, x_7, x_8, x_626);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_636; 
x_628 = lean_ctor_get(x_627, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_629 = x_627;
} else {
 lean_dec_ref(x_627);
 x_629 = lean_box(0);
}
x_636 = l_Lean_Expr_getAppFn___main(x_625);
if (lean_obj_tag(x_636) == 4)
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_625);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
lean_dec(x_636);
if (lean_is_scalar(x_629)) {
 x_638 = lean_alloc_ctor(0, 2, 0);
} else {
 x_638 = x_629;
}
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_628);
return x_638;
}
else
{
lean_object* x_639; 
lean_dec(x_636);
lean_dec(x_629);
x_639 = lean_box(0);
x_630 = x_639;
goto block_635;
}
block_635:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_630);
x_631 = l_Lean_indentExpr(x_625);
x_632 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_633 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
x_634 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_633, x_3, x_4, x_5, x_6, x_7, x_8, x_628);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_634;
}
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_625);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_640 = lean_ctor_get(x_627, 0);
lean_inc(x_640);
x_641 = lean_ctor_get(x_627, 1);
lean_inc(x_641);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_642 = x_627;
} else {
 lean_dec_ref(x_627);
 x_642 = lean_box(0);
}
if (lean_is_scalar(x_642)) {
 x_643 = lean_alloc_ctor(1, 2, 0);
} else {
 x_643 = x_642;
}
lean_ctor_set(x_643, 0, x_640);
lean_ctor_set(x_643, 1, x_641);
return x_643;
}
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_644 = lean_ctor_get(x_624, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_624, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 lean_ctor_release(x_624, 1);
 x_646 = x_624;
} else {
 lean_dec_ref(x_624);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_648 = lean_ctor_get(x_621, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_621, 1);
lean_inc(x_649);
if (lean_is_exclusive(x_621)) {
 lean_ctor_release(x_621, 0);
 lean_ctor_release(x_621, 1);
 x_650 = x_621;
} else {
 lean_dec_ref(x_621);
 x_650 = lean_box(0);
}
if (lean_is_scalar(x_650)) {
 x_651 = lean_alloc_ctor(1, 2, 0);
} else {
 x_651 = x_650;
}
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_649);
return x_651;
}
}
else
{
lean_object* x_652; 
lean_dec(x_2);
x_652 = lean_box(0);
x_613 = x_652;
goto block_618;
}
}
case 1:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_653; lean_object* x_654; 
lean_dec(x_70);
x_653 = lean_ctor_get(x_2, 1);
lean_inc(x_653);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_654 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_653, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_654, 0);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 1);
lean_inc(x_656);
lean_dec(x_654);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_657 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_655, x_3, x_4, x_5, x_6, x_7, x_8, x_656);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_657, 1);
lean_inc(x_659);
lean_dec(x_657);
lean_inc(x_3);
lean_inc(x_658);
x_660 = l_Lean_Elab_Term_tryPostponeIfMVar(x_658, x_3, x_4, x_5, x_6, x_7, x_8, x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_669; 
x_661 = lean_ctor_get(x_660, 1);
lean_inc(x_661);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_662 = x_660;
} else {
 lean_dec_ref(x_660);
 x_662 = lean_box(0);
}
x_669 = l_Lean_Expr_getAppFn___main(x_658);
if (lean_obj_tag(x_669) == 4)
{
lean_object* x_670; lean_object* x_671; 
lean_dec(x_658);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
lean_dec(x_669);
if (lean_is_scalar(x_662)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_662;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_661);
return x_671;
}
else
{
lean_object* x_672; 
lean_dec(x_669);
lean_dec(x_662);
x_672 = lean_box(0);
x_663 = x_672;
goto block_668;
}
block_668:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
lean_dec(x_663);
x_664 = l_Lean_indentExpr(x_658);
x_665 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_666 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_666, 0, x_665);
lean_ctor_set(x_666, 1, x_664);
x_667 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_666, x_3, x_4, x_5, x_6, x_7, x_8, x_661);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_667;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_658);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_673 = lean_ctor_get(x_660, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_660, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_675 = x_660;
} else {
 lean_dec_ref(x_660);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_677 = lean_ctor_get(x_657, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_657, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_657)) {
 lean_ctor_release(x_657, 0);
 lean_ctor_release(x_657, 1);
 x_679 = x_657;
} else {
 lean_dec_ref(x_657);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_681 = lean_ctor_get(x_654, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_654, 1);
lean_inc(x_682);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_683 = x_654;
} else {
 lean_dec_ref(x_654);
 x_683 = lean_box(0);
}
if (lean_is_scalar(x_683)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_683;
}
lean_ctor_set(x_684, 0, x_681);
lean_ctor_set(x_684, 1, x_682);
return x_684;
}
}
else
{
lean_object* x_685; 
lean_dec(x_2);
x_685 = lean_box(0);
x_613 = x_685;
goto block_618;
}
}
case 2:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_686; lean_object* x_687; 
lean_dec(x_70);
x_686 = lean_ctor_get(x_2, 1);
lean_inc(x_686);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_687 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_686, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
lean_dec(x_687);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_690 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_688, x_3, x_4, x_5, x_6, x_7, x_8, x_689);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
lean_dec(x_690);
lean_inc(x_3);
lean_inc(x_691);
x_693 = l_Lean_Elab_Term_tryPostponeIfMVar(x_691, x_3, x_4, x_5, x_6, x_7, x_8, x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_702; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_695 = x_693;
} else {
 lean_dec_ref(x_693);
 x_695 = lean_box(0);
}
x_702 = l_Lean_Expr_getAppFn___main(x_691);
if (lean_obj_tag(x_702) == 4)
{
lean_object* x_703; lean_object* x_704; 
lean_dec(x_691);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
lean_dec(x_702);
if (lean_is_scalar(x_695)) {
 x_704 = lean_alloc_ctor(0, 2, 0);
} else {
 x_704 = x_695;
}
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_694);
return x_704;
}
else
{
lean_object* x_705; 
lean_dec(x_702);
lean_dec(x_695);
x_705 = lean_box(0);
x_696 = x_705;
goto block_701;
}
block_701:
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_696);
x_697 = l_Lean_indentExpr(x_691);
x_698 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_699 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_697);
x_700 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_699, x_3, x_4, x_5, x_6, x_7, x_8, x_694);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_700;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_691);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_706 = lean_ctor_get(x_693, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_693, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_708 = x_693;
} else {
 lean_dec_ref(x_693);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_710 = lean_ctor_get(x_690, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_690, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_712 = x_690;
} else {
 lean_dec_ref(x_690);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_711);
return x_713;
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_714 = lean_ctor_get(x_687, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_687, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_716 = x_687;
} else {
 lean_dec_ref(x_687);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_714);
lean_ctor_set(x_717, 1, x_715);
return x_717;
}
}
else
{
lean_object* x_718; 
lean_dec(x_2);
x_718 = lean_box(0);
x_613 = x_718;
goto block_618;
}
}
case 3:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_719; lean_object* x_720; 
lean_dec(x_70);
x_719 = lean_ctor_get(x_2, 1);
lean_inc(x_719);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_720 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_719, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_723 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_721, x_3, x_4, x_5, x_6, x_7, x_8, x_722);
if (lean_obj_tag(x_723) == 0)
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
lean_inc(x_3);
lean_inc(x_724);
x_726 = l_Lean_Elab_Term_tryPostponeIfMVar(x_724, x_3, x_4, x_5, x_6, x_7, x_8, x_725);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_735; 
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_728 = x_726;
} else {
 lean_dec_ref(x_726);
 x_728 = lean_box(0);
}
x_735 = l_Lean_Expr_getAppFn___main(x_724);
if (lean_obj_tag(x_735) == 4)
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_724);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_736 = lean_ctor_get(x_735, 0);
lean_inc(x_736);
lean_dec(x_735);
if (lean_is_scalar(x_728)) {
 x_737 = lean_alloc_ctor(0, 2, 0);
} else {
 x_737 = x_728;
}
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_727);
return x_737;
}
else
{
lean_object* x_738; 
lean_dec(x_735);
lean_dec(x_728);
x_738 = lean_box(0);
x_729 = x_738;
goto block_734;
}
block_734:
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_729);
x_730 = l_Lean_indentExpr(x_724);
x_731 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_732 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_730);
x_733 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_732, x_3, x_4, x_5, x_6, x_7, x_8, x_727);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_733;
}
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_724);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_739 = lean_ctor_get(x_726, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_726, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_741 = x_726;
} else {
 lean_dec_ref(x_726);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_743 = lean_ctor_get(x_723, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_723, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_723)) {
 lean_ctor_release(x_723, 0);
 lean_ctor_release(x_723, 1);
 x_745 = x_723;
} else {
 lean_dec_ref(x_723);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 2, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_747 = lean_ctor_get(x_720, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_720, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_749 = x_720;
} else {
 lean_dec_ref(x_720);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; 
lean_dec(x_2);
x_751 = lean_box(0);
x_613 = x_751;
goto block_618;
}
}
case 4:
{
lean_object* x_752; lean_object* x_753; 
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_752 = lean_ctor_get(x_619, 0);
lean_inc(x_752);
lean_dec(x_619);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_612);
return x_753;
}
case 5:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_754; lean_object* x_755; 
lean_dec(x_70);
x_754 = lean_ctor_get(x_2, 1);
lean_inc(x_754);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_755 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_754, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
lean_dec(x_755);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_758 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_756, x_3, x_4, x_5, x_6, x_7, x_8, x_757);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_759 = lean_ctor_get(x_758, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_758, 1);
lean_inc(x_760);
lean_dec(x_758);
lean_inc(x_3);
lean_inc(x_759);
x_761 = l_Lean_Elab_Term_tryPostponeIfMVar(x_759, x_3, x_4, x_5, x_6, x_7, x_8, x_760);
if (lean_obj_tag(x_761) == 0)
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_770; 
x_762 = lean_ctor_get(x_761, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_763 = x_761;
} else {
 lean_dec_ref(x_761);
 x_763 = lean_box(0);
}
x_770 = l_Lean_Expr_getAppFn___main(x_759);
if (lean_obj_tag(x_770) == 4)
{
lean_object* x_771; lean_object* x_772; 
lean_dec(x_759);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
lean_dec(x_770);
if (lean_is_scalar(x_763)) {
 x_772 = lean_alloc_ctor(0, 2, 0);
} else {
 x_772 = x_763;
}
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set(x_772, 1, x_762);
return x_772;
}
else
{
lean_object* x_773; 
lean_dec(x_770);
lean_dec(x_763);
x_773 = lean_box(0);
x_764 = x_773;
goto block_769;
}
block_769:
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_764);
x_765 = l_Lean_indentExpr(x_759);
x_766 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_767 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_765);
x_768 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_767, x_3, x_4, x_5, x_6, x_7, x_8, x_762);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_768;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_759);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_774 = lean_ctor_get(x_761, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_761, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_761)) {
 lean_ctor_release(x_761, 0);
 lean_ctor_release(x_761, 1);
 x_776 = x_761;
} else {
 lean_dec_ref(x_761);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(1, 2, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_774);
lean_ctor_set(x_777, 1, x_775);
return x_777;
}
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_778 = lean_ctor_get(x_758, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_758, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_758)) {
 lean_ctor_release(x_758, 0);
 lean_ctor_release(x_758, 1);
 x_780 = x_758;
} else {
 lean_dec_ref(x_758);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_778);
lean_ctor_set(x_781, 1, x_779);
return x_781;
}
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_782 = lean_ctor_get(x_755, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_755, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_784 = x_755;
} else {
 lean_dec_ref(x_755);
 x_784 = lean_box(0);
}
if (lean_is_scalar(x_784)) {
 x_785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_785 = x_784;
}
lean_ctor_set(x_785, 0, x_782);
lean_ctor_set(x_785, 1, x_783);
return x_785;
}
}
else
{
lean_object* x_786; 
lean_dec(x_2);
x_786 = lean_box(0);
x_613 = x_786;
goto block_618;
}
}
case 6:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_787; lean_object* x_788; 
lean_dec(x_70);
x_787 = lean_ctor_get(x_2, 1);
lean_inc(x_787);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_788 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_787, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
x_789 = lean_ctor_get(x_788, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_788, 1);
lean_inc(x_790);
lean_dec(x_788);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_791 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_789, x_3, x_4, x_5, x_6, x_7, x_8, x_790);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_ctor_get(x_791, 1);
lean_inc(x_793);
lean_dec(x_791);
lean_inc(x_3);
lean_inc(x_792);
x_794 = l_Lean_Elab_Term_tryPostponeIfMVar(x_792, x_3, x_4, x_5, x_6, x_7, x_8, x_793);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_803; 
x_795 = lean_ctor_get(x_794, 1);
lean_inc(x_795);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 x_796 = x_794;
} else {
 lean_dec_ref(x_794);
 x_796 = lean_box(0);
}
x_803 = l_Lean_Expr_getAppFn___main(x_792);
if (lean_obj_tag(x_803) == 4)
{
lean_object* x_804; lean_object* x_805; 
lean_dec(x_792);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
lean_dec(x_803);
if (lean_is_scalar(x_796)) {
 x_805 = lean_alloc_ctor(0, 2, 0);
} else {
 x_805 = x_796;
}
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_795);
return x_805;
}
else
{
lean_object* x_806; 
lean_dec(x_803);
lean_dec(x_796);
x_806 = lean_box(0);
x_797 = x_806;
goto block_802;
}
block_802:
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_797);
x_798 = l_Lean_indentExpr(x_792);
x_799 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_800 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_798);
x_801 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_800, x_3, x_4, x_5, x_6, x_7, x_8, x_795);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_801;
}
}
else
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
lean_dec(x_792);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_807 = lean_ctor_get(x_794, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_794, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_794)) {
 lean_ctor_release(x_794, 0);
 lean_ctor_release(x_794, 1);
 x_809 = x_794;
} else {
 lean_dec_ref(x_794);
 x_809 = lean_box(0);
}
if (lean_is_scalar(x_809)) {
 x_810 = lean_alloc_ctor(1, 2, 0);
} else {
 x_810 = x_809;
}
lean_ctor_set(x_810, 0, x_807);
lean_ctor_set(x_810, 1, x_808);
return x_810;
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_811 = lean_ctor_get(x_791, 0);
lean_inc(x_811);
x_812 = lean_ctor_get(x_791, 1);
lean_inc(x_812);
if (lean_is_exclusive(x_791)) {
 lean_ctor_release(x_791, 0);
 lean_ctor_release(x_791, 1);
 x_813 = x_791;
} else {
 lean_dec_ref(x_791);
 x_813 = lean_box(0);
}
if (lean_is_scalar(x_813)) {
 x_814 = lean_alloc_ctor(1, 2, 0);
} else {
 x_814 = x_813;
}
lean_ctor_set(x_814, 0, x_811);
lean_ctor_set(x_814, 1, x_812);
return x_814;
}
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_815 = lean_ctor_get(x_788, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_788, 1);
lean_inc(x_816);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 lean_ctor_release(x_788, 1);
 x_817 = x_788;
} else {
 lean_dec_ref(x_788);
 x_817 = lean_box(0);
}
if (lean_is_scalar(x_817)) {
 x_818 = lean_alloc_ctor(1, 2, 0);
} else {
 x_818 = x_817;
}
lean_ctor_set(x_818, 0, x_815);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
lean_object* x_819; 
lean_dec(x_2);
x_819 = lean_box(0);
x_613 = x_819;
goto block_618;
}
}
case 7:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_820; lean_object* x_821; 
lean_dec(x_70);
x_820 = lean_ctor_get(x_2, 1);
lean_inc(x_820);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_821 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_820, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_824 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_822, x_3, x_4, x_5, x_6, x_7, x_8, x_823);
if (lean_obj_tag(x_824) == 0)
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_825 = lean_ctor_get(x_824, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_824, 1);
lean_inc(x_826);
lean_dec(x_824);
lean_inc(x_3);
lean_inc(x_825);
x_827 = l_Lean_Elab_Term_tryPostponeIfMVar(x_825, x_3, x_4, x_5, x_6, x_7, x_8, x_826);
if (lean_obj_tag(x_827) == 0)
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_836; 
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_829 = x_827;
} else {
 lean_dec_ref(x_827);
 x_829 = lean_box(0);
}
x_836 = l_Lean_Expr_getAppFn___main(x_825);
if (lean_obj_tag(x_836) == 4)
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_825);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_837 = lean_ctor_get(x_836, 0);
lean_inc(x_837);
lean_dec(x_836);
if (lean_is_scalar(x_829)) {
 x_838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_838 = x_829;
}
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_828);
return x_838;
}
else
{
lean_object* x_839; 
lean_dec(x_836);
lean_dec(x_829);
x_839 = lean_box(0);
x_830 = x_839;
goto block_835;
}
block_835:
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_830);
x_831 = l_Lean_indentExpr(x_825);
x_832 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_833 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_831);
x_834 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_833, x_3, x_4, x_5, x_6, x_7, x_8, x_828);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_834;
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_825);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_840 = lean_ctor_get(x_827, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_827, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_842 = x_827;
} else {
 lean_dec_ref(x_827);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(1, 2, 0);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_840);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_844 = lean_ctor_get(x_824, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_824, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_824)) {
 lean_ctor_release(x_824, 0);
 lean_ctor_release(x_824, 1);
 x_846 = x_824;
} else {
 lean_dec_ref(x_824);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_844);
lean_ctor_set(x_847, 1, x_845);
return x_847;
}
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_848 = lean_ctor_get(x_821, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_821, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_850 = x_821;
} else {
 lean_dec_ref(x_821);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
else
{
lean_object* x_852; 
lean_dec(x_2);
x_852 = lean_box(0);
x_613 = x_852;
goto block_618;
}
}
case 8:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_853; lean_object* x_854; 
lean_dec(x_70);
x_853 = lean_ctor_get(x_2, 1);
lean_inc(x_853);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_854 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_853, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_854) == 0)
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_855 = lean_ctor_get(x_854, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_854, 1);
lean_inc(x_856);
lean_dec(x_854);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_857 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_855, x_3, x_4, x_5, x_6, x_7, x_8, x_856);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
lean_inc(x_3);
lean_inc(x_858);
x_860 = l_Lean_Elab_Term_tryPostponeIfMVar(x_858, x_3, x_4, x_5, x_6, x_7, x_8, x_859);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_869; 
x_861 = lean_ctor_get(x_860, 1);
lean_inc(x_861);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_862 = x_860;
} else {
 lean_dec_ref(x_860);
 x_862 = lean_box(0);
}
x_869 = l_Lean_Expr_getAppFn___main(x_858);
if (lean_obj_tag(x_869) == 4)
{
lean_object* x_870; lean_object* x_871; 
lean_dec(x_858);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
lean_dec(x_869);
if (lean_is_scalar(x_862)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_862;
}
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_861);
return x_871;
}
else
{
lean_object* x_872; 
lean_dec(x_869);
lean_dec(x_862);
x_872 = lean_box(0);
x_863 = x_872;
goto block_868;
}
block_868:
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_863);
x_864 = l_Lean_indentExpr(x_858);
x_865 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_866 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_864);
x_867 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_866, x_3, x_4, x_5, x_6, x_7, x_8, x_861);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_867;
}
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_dec(x_858);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_873 = lean_ctor_get(x_860, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_860, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_875 = x_860;
} else {
 lean_dec_ref(x_860);
 x_875 = lean_box(0);
}
if (lean_is_scalar(x_875)) {
 x_876 = lean_alloc_ctor(1, 2, 0);
} else {
 x_876 = x_875;
}
lean_ctor_set(x_876, 0, x_873);
lean_ctor_set(x_876, 1, x_874);
return x_876;
}
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_877 = lean_ctor_get(x_857, 0);
lean_inc(x_877);
x_878 = lean_ctor_get(x_857, 1);
lean_inc(x_878);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_879 = x_857;
} else {
 lean_dec_ref(x_857);
 x_879 = lean_box(0);
}
if (lean_is_scalar(x_879)) {
 x_880 = lean_alloc_ctor(1, 2, 0);
} else {
 x_880 = x_879;
}
lean_ctor_set(x_880, 0, x_877);
lean_ctor_set(x_880, 1, x_878);
return x_880;
}
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_881 = lean_ctor_get(x_854, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_854, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_854)) {
 lean_ctor_release(x_854, 0);
 lean_ctor_release(x_854, 1);
 x_883 = x_854;
} else {
 lean_dec_ref(x_854);
 x_883 = lean_box(0);
}
if (lean_is_scalar(x_883)) {
 x_884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_884 = x_883;
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_882);
return x_884;
}
}
else
{
lean_object* x_885; 
lean_dec(x_2);
x_885 = lean_box(0);
x_613 = x_885;
goto block_618;
}
}
case 9:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_886; lean_object* x_887; 
lean_dec(x_70);
x_886 = lean_ctor_get(x_2, 1);
lean_inc(x_886);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_887 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_886, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_890 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_888, x_3, x_4, x_5, x_6, x_7, x_8, x_889);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_890, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_890, 1);
lean_inc(x_892);
lean_dec(x_890);
lean_inc(x_3);
lean_inc(x_891);
x_893 = l_Lean_Elab_Term_tryPostponeIfMVar(x_891, x_3, x_4, x_5, x_6, x_7, x_8, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_902; 
x_894 = lean_ctor_get(x_893, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_895 = x_893;
} else {
 lean_dec_ref(x_893);
 x_895 = lean_box(0);
}
x_902 = l_Lean_Expr_getAppFn___main(x_891);
if (lean_obj_tag(x_902) == 4)
{
lean_object* x_903; lean_object* x_904; 
lean_dec(x_891);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
lean_dec(x_902);
if (lean_is_scalar(x_895)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_895;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_894);
return x_904;
}
else
{
lean_object* x_905; 
lean_dec(x_902);
lean_dec(x_895);
x_905 = lean_box(0);
x_896 = x_905;
goto block_901;
}
block_901:
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_896);
x_897 = l_Lean_indentExpr(x_891);
x_898 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_899 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_897);
x_900 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_899, x_3, x_4, x_5, x_6, x_7, x_8, x_894);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_900;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_891);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_906 = lean_ctor_get(x_893, 0);
lean_inc(x_906);
x_907 = lean_ctor_get(x_893, 1);
lean_inc(x_907);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_908 = x_893;
} else {
 lean_dec_ref(x_893);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_910 = lean_ctor_get(x_890, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_890, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_912 = x_890;
} else {
 lean_dec_ref(x_890);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_914 = lean_ctor_get(x_887, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_887, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_916 = x_887;
} else {
 lean_dec_ref(x_887);
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
x_613 = x_918;
goto block_618;
}
}
case 10:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_919; lean_object* x_920; 
lean_dec(x_70);
x_919 = lean_ctor_get(x_2, 1);
lean_inc(x_919);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_920 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_919, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_920) == 0)
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_921 = lean_ctor_get(x_920, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_920, 1);
lean_inc(x_922);
lean_dec(x_920);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_923 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_921, x_3, x_4, x_5, x_6, x_7, x_8, x_922);
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
x_926 = l_Lean_Elab_Term_tryPostponeIfMVar(x_924, x_3, x_4, x_5, x_6, x_7, x_8, x_925);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_935; 
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
x_935 = l_Lean_Expr_getAppFn___main(x_924);
if (lean_obj_tag(x_935) == 4)
{
lean_object* x_936; lean_object* x_937; 
lean_dec(x_924);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_936 = lean_ctor_get(x_935, 0);
lean_inc(x_936);
lean_dec(x_935);
if (lean_is_scalar(x_928)) {
 x_937 = lean_alloc_ctor(0, 2, 0);
} else {
 x_937 = x_928;
}
lean_ctor_set(x_937, 0, x_936);
lean_ctor_set(x_937, 1, x_927);
return x_937;
}
else
{
lean_object* x_938; 
lean_dec(x_935);
lean_dec(x_928);
x_938 = lean_box(0);
x_929 = x_938;
goto block_934;
}
block_934:
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_dec(x_929);
x_930 = l_Lean_indentExpr(x_924);
x_931 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_932 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_932, 0, x_931);
lean_ctor_set(x_932, 1, x_930);
x_933 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_932, x_3, x_4, x_5, x_6, x_7, x_8, x_927);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_933;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_924);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_939 = lean_ctor_get(x_926, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_926, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_926)) {
 lean_ctor_release(x_926, 0);
 lean_ctor_release(x_926, 1);
 x_941 = x_926;
} else {
 lean_dec_ref(x_926);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_940);
return x_942;
}
}
else
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_943 = lean_ctor_get(x_923, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_923, 1);
lean_inc(x_944);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_945 = x_923;
} else {
 lean_dec_ref(x_923);
 x_945 = lean_box(0);
}
if (lean_is_scalar(x_945)) {
 x_946 = lean_alloc_ctor(1, 2, 0);
} else {
 x_946 = x_945;
}
lean_ctor_set(x_946, 0, x_943);
lean_ctor_set(x_946, 1, x_944);
return x_946;
}
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_947 = lean_ctor_get(x_920, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_920, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_920)) {
 lean_ctor_release(x_920, 0);
 lean_ctor_release(x_920, 1);
 x_949 = x_920;
} else {
 lean_dec_ref(x_920);
 x_949 = lean_box(0);
}
if (lean_is_scalar(x_949)) {
 x_950 = lean_alloc_ctor(1, 2, 0);
} else {
 x_950 = x_949;
}
lean_ctor_set(x_950, 0, x_947);
lean_ctor_set(x_950, 1, x_948);
return x_950;
}
}
else
{
lean_object* x_951; 
lean_dec(x_2);
x_951 = lean_box(0);
x_613 = x_951;
goto block_618;
}
}
case 11:
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_70);
x_952 = lean_ctor_get(x_2, 1);
lean_inc(x_952);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_953 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_952, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_953, 1);
lean_inc(x_955);
lean_dec(x_953);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_956 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_954, x_3, x_4, x_5, x_6, x_7, x_8, x_955);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
lean_dec(x_956);
lean_inc(x_3);
lean_inc(x_957);
x_959 = l_Lean_Elab_Term_tryPostponeIfMVar(x_957, x_3, x_4, x_5, x_6, x_7, x_8, x_958);
if (lean_obj_tag(x_959) == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_968; 
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_961 = x_959;
} else {
 lean_dec_ref(x_959);
 x_961 = lean_box(0);
}
x_968 = l_Lean_Expr_getAppFn___main(x_957);
if (lean_obj_tag(x_968) == 4)
{
lean_object* x_969; lean_object* x_970; 
lean_dec(x_957);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
lean_dec(x_968);
if (lean_is_scalar(x_961)) {
 x_970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_970 = x_961;
}
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_960);
return x_970;
}
else
{
lean_object* x_971; 
lean_dec(x_968);
lean_dec(x_961);
x_971 = lean_box(0);
x_962 = x_971;
goto block_967;
}
block_967:
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_962);
x_963 = l_Lean_indentExpr(x_957);
x_964 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_965 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_963);
x_966 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_965, x_3, x_4, x_5, x_6, x_7, x_8, x_960);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_966;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
lean_dec(x_957);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_972 = lean_ctor_get(x_959, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_959, 1);
lean_inc(x_973);
if (lean_is_exclusive(x_959)) {
 lean_ctor_release(x_959, 0);
 lean_ctor_release(x_959, 1);
 x_974 = x_959;
} else {
 lean_dec_ref(x_959);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_972);
lean_ctor_set(x_975, 1, x_973);
return x_975;
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_976 = lean_ctor_get(x_956, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_956, 1);
lean_inc(x_977);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_978 = x_956;
} else {
 lean_dec_ref(x_956);
 x_978 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_979 = lean_alloc_ctor(1, 2, 0);
} else {
 x_979 = x_978;
}
lean_ctor_set(x_979, 0, x_976);
lean_ctor_set(x_979, 1, x_977);
return x_979;
}
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_980 = lean_ctor_get(x_953, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_953, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_953)) {
 lean_ctor_release(x_953, 0);
 lean_ctor_release(x_953, 1);
 x_982 = x_953;
} else {
 lean_dec_ref(x_953);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_982)) {
 x_983 = lean_alloc_ctor(1, 2, 0);
} else {
 x_983 = x_982;
}
lean_ctor_set(x_983, 0, x_980);
lean_ctor_set(x_983, 1, x_981);
return x_983;
}
}
else
{
lean_object* x_984; 
lean_dec(x_2);
x_984 = lean_box(0);
x_613 = x_984;
goto block_618;
}
}
default: 
{
lean_dec(x_619);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_985; lean_object* x_986; 
lean_dec(x_70);
x_985 = lean_ctor_get(x_2, 1);
lean_inc(x_985);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_986 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_985, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
if (lean_obj_tag(x_986) == 0)
{
lean_object* x_987; lean_object* x_988; lean_object* x_989; 
x_987 = lean_ctor_get(x_986, 0);
lean_inc(x_987);
x_988 = lean_ctor_get(x_986, 1);
lean_inc(x_988);
lean_dec(x_986);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_989 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_7__isTypeApp_x3f___spec__1(x_987, x_3, x_4, x_5, x_6, x_7, x_8, x_988);
if (lean_obj_tag(x_989) == 0)
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_989, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_989, 1);
lean_inc(x_991);
lean_dec(x_989);
lean_inc(x_3);
lean_inc(x_990);
x_992 = l_Lean_Elab_Term_tryPostponeIfMVar(x_990, x_3, x_4, x_5, x_6, x_7, x_8, x_991);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_1001; 
x_993 = lean_ctor_get(x_992, 1);
lean_inc(x_993);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_994 = x_992;
} else {
 lean_dec_ref(x_992);
 x_994 = lean_box(0);
}
x_1001 = l_Lean_Expr_getAppFn___main(x_990);
if (lean_obj_tag(x_1001) == 4)
{
lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_990);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
lean_dec(x_1001);
if (lean_is_scalar(x_994)) {
 x_1003 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1003 = x_994;
}
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_993);
return x_1003;
}
else
{
lean_object* x_1004; 
lean_dec(x_1001);
lean_dec(x_994);
x_1004 = lean_box(0);
x_995 = x_1004;
goto block_1000;
}
block_1000:
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; 
lean_dec(x_995);
x_996 = l_Lean_indentExpr(x_990);
x_997 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__6;
x_998 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
x_999 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_998, x_3, x_4, x_5, x_6, x_7, x_8, x_993);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_999;
}
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_990);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1005 = lean_ctor_get(x_992, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_992, 1);
lean_inc(x_1006);
if (lean_is_exclusive(x_992)) {
 lean_ctor_release(x_992, 0);
 lean_ctor_release(x_992, 1);
 x_1007 = x_992;
} else {
 lean_dec_ref(x_992);
 x_1007 = lean_box(0);
}
if (lean_is_scalar(x_1007)) {
 x_1008 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1008 = x_1007;
}
lean_ctor_set(x_1008, 0, x_1005);
lean_ctor_set(x_1008, 1, x_1006);
return x_1008;
}
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1009 = lean_ctor_get(x_989, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_989, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_989)) {
 lean_ctor_release(x_989, 0);
 lean_ctor_release(x_989, 1);
 x_1011 = x_989;
} else {
 lean_dec_ref(x_989);
 x_1011 = lean_box(0);
}
if (lean_is_scalar(x_1011)) {
 x_1012 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1012 = x_1011;
}
lean_ctor_set(x_1012, 0, x_1009);
lean_ctor_set(x_1012, 1, x_1010);
return x_1012;
}
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_1013 = lean_ctor_get(x_986, 0);
lean_inc(x_1013);
x_1014 = lean_ctor_get(x_986, 1);
lean_inc(x_1014);
if (lean_is_exclusive(x_986)) {
 lean_ctor_release(x_986, 0);
 lean_ctor_release(x_986, 1);
 x_1015 = x_986;
} else {
 lean_dec_ref(x_986);
 x_1015 = lean_box(0);
}
if (lean_is_scalar(x_1015)) {
 x_1016 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1016 = x_1015;
}
lean_ctor_set(x_1016, 0, x_1013);
lean_ctor_set(x_1016, 1, x_1014);
return x_1016;
}
}
else
{
lean_object* x_1017; 
lean_dec(x_2);
x_1017 = lean_box(0);
x_613 = x_1017;
goto block_618;
}
}
}
block_618:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_613);
x_614 = l_Lean_indentExpr(x_70);
x_615 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_616 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_614);
x_617 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_616, x_3, x_4, x_5, x_6, x_7, x_8, x_612);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_617;
}
}
}
else
{
uint8_t x_1018; 
lean_dec(x_70);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_1018 = !lean_is_exclusive(x_71);
if (x_1018 == 0)
{
return x_71;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_71, 0);
x_1020 = lean_ctor_get(x_71, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_71);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
block_25:
{
lean_dec(x_12);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Expr_Inhabited;
x_14 = l_Option_get_x21___rarg___closed__3;
x_15 = lean_panic_fn(x_13, x_14);
x_16 = l_Lean_indentExpr(x_15);
x_17 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_indentExpr(x_20);
x_22 = l___private_Lean_Elab_StructInst_5__getStructName___rarg___closed__3;
x_23 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_24;
}
}
}
else
{
uint8_t x_1022; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_10);
if (x_1022 == 0)
{
return x_10;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_10, 0);
x_1024 = lean_ctor_get(x_10, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_10);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_StructInst_5__getStructName___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_5__getStructName___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_4);
return x_10;
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
uint8_t l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(uint8_t x_1, lean_object* x_2) {
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
x_5 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_1, x_4);
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
x_9 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_8);
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
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault___main(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = 1;
x_4 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_3, x_2);
return x_4;
}
}
lean_object* l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_foldr___main___at_Lean_Elab_Term_StructInst_Struct_allDefault___main___spec__1(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Term_StructInst_Struct_allDefault___main___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Term_StructInst_Struct_allDefault(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
return x_2;
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
x_1 = l___private_Lean_Elab_Binders_16__expandMatchAltsIntoMatchAux___main___closed__11;
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
x_5 = l_System_FilePath_dirName___closed__1;
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
x_17 = l_System_FilePath_dirName___closed__1;
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
x_3 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__2;
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
lean_object* _init_l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstField");
return x_1;
}
}
lean_object* _init_l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__6;
x_2 = l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
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
x_9 = l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2;
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
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
x_49 = l_Lean_Name_inhabited;
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
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
x_51 = l_Nat_repr(x_45);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
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
x_63 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_64 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_41);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_31, 0);
x_70 = lean_ctor_get(x_31, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_31);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_70, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_array_get_size(x_1);
x_74 = lean_nat_dec_lt(x_73, x_70);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_sub(x_70, x_75);
lean_dec(x_70);
x_77 = l_Lean_Name_inhabited;
x_78 = lean_array_get(x_77, x_1, x_76);
lean_dec(x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set(x_30, 0, x_79);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_70);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_80 = l_Nat_repr(x_73);
x_81 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_69, x_86, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_69);
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
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_70);
lean_free_object(x_30);
lean_dec(x_38);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_92 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_93 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_69, x_92, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_69);
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
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_30, 1);
lean_inc(x_98);
lean_dec(x_30);
x_99 = lean_ctor_get(x_31, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_31, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_101 = x_31;
} else {
 lean_dec_ref(x_31);
 x_101 = lean_box(0);
}
x_102 = lean_unsigned_to_nat(0u);
x_103 = lean_nat_dec_eq(x_100, x_102);
if (x_103 == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_array_get_size(x_1);
x_105 = lean_nat_dec_lt(x_104, x_100);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_sub(x_100, x_106);
lean_dec(x_100);
x_108 = l_Lean_Name_inhabited;
x_109 = lean_array_get(x_108, x_1, x_107);
lean_dec(x_107);
if (lean_is_scalar(x_101)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_101;
 lean_ctor_set_tag(x_110, 0);
}
lean_ctor_set(x_110, 0, x_99);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_98);
lean_ctor_set(x_12, 1, x_111);
x_15 = x_12;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_112 = l_Nat_repr(x_104);
x_113 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_116 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_99, x_118, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_99);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
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
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_free_object(x_12);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_14);
lean_dec(x_13);
x_124 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_125 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_99, x_124, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_99);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
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
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_130 = lean_ctor_get(x_12, 0);
x_131 = lean_ctor_get(x_12, 2);
x_132 = lean_ctor_get(x_12, 3);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_12);
x_133 = lean_ctor_get(x_30, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_134 = x_30;
} else {
 lean_dec_ref(x_30);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_31, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_31, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_137 = x_31;
} else {
 lean_dec_ref(x_31);
 x_137 = lean_box(0);
}
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_eq(x_136, x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_array_get_size(x_1);
x_141 = lean_nat_dec_lt(x_140, x_136);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_140);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_sub(x_136, x_142);
lean_dec(x_136);
x_144 = l_Lean_Name_inhabited;
x_145 = lean_array_get(x_144, x_1, x_143);
lean_dec(x_143);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_137;
 lean_ctor_set_tag(x_146, 0);
}
lean_ctor_set(x_146, 0, x_135);
lean_ctor_set(x_146, 1, x_145);
if (lean_is_scalar(x_134)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_134;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_133);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_130);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set(x_148, 2, x_131);
lean_ctor_set(x_148, 3, x_132);
x_15 = x_148;
x_16 = x_9;
goto block_29;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_14);
lean_dec(x_13);
x_149 = l_Nat_repr(x_140);
x_150 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__3;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__6;
x_155 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_135, x_155, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_135);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_14);
lean_dec(x_13);
x_161 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___closed__9;
x_162 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_135, x_161, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_135);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
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
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
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
lean_object* l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
return x_16;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed), 9, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___main___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_9__expandNumLitFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
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
x_39 = l_Lean_findField_x3f___main(x_2, x_38, x_37);
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
x_41 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__3;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_38);
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_47, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_62 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_65 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_65, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_72 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_36, x_71);
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
x_76 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__6;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___closed__9;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_36, x_79, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_86 = l_List_map___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__1(x_36, x_85);
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
x_18 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
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
lean_object* l___private_Lean_Elab_StructInst_10__expandParentFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed), 10, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_14;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_mapM___main___at___private_Lean_Elab_StructInst_10__expandParentFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_15 = l_unreachable_x21___rarg(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = lean_apply_7(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_1 = x_17;
x_2 = x_13;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
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
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_dec(x_26);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_box(0);
lean_ctor_set(x_12, 1, x_30);
lean_ctor_set(x_12, 0, x_11);
x_31 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_31;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_11);
x_34 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_34;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
x_37 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_36);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; 
lean_ctor_set(x_12, 1, x_33);
lean_ctor_set(x_12, 0, x_11);
x_39 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_28, x_12);
x_1 = x_39;
x_2 = x_27;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_1);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_28);
x_43 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_41, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_41);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_27);
lean_free_object(x_12);
lean_dec(x_1);
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_28);
x_54 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_52, x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_52);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_free_object(x_12);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_1);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_dec(x_2);
x_64 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_65 = l_unreachable_x21___rarg(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_66 = lean_apply_7(x_65, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_1 = x_67;
x_2 = x_63;
x_9 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_12, 0);
lean_inc(x_74);
lean_dec(x_12);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Std_HashMapImp_find_x3f___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__1(x_1, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_11);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_79);
x_1 = x_80;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_77, 0);
lean_inc(x_82);
lean_dec(x_77);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_11);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_83);
x_1 = x_84;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
x_87 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_11);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Elab_Term_StructInst_Field_isSimple___rarg(x_86);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_11);
lean_ctor_set(x_89, 1, x_82);
x_90 = l_Std_HashMapImp_insert___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__3(x_1, x_76, x_89);
x_1 = x_90;
x_2 = x_75;
goto _start;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_82);
lean_dec(x_75);
lean_dec(x_1);
x_92 = lean_ctor_get(x_11, 0);
lean_inc(x_92);
lean_dec(x_11);
x_93 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_93, 0, x_76);
x_94 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_96 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_97 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_92, x_97, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_92);
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
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_86);
lean_dec(x_82);
lean_dec(x_75);
lean_dec(x_1);
x_103 = lean_ctor_get(x_11, 0);
lean_inc(x_103);
lean_dec(x_11);
x_104 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_104, 0, x_76);
x_105 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_106 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__6;
x_108 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_103, x_108, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_103);
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
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_74);
lean_dec(x_11);
lean_dec(x_1);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_dec(x_2);
x_115 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_116 = l_unreachable_x21___rarg(x_115);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_117 = lean_apply_7(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_1 = x_118;
x_2 = x_114;
x_9 = x_119;
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_114);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_ctor_get(x_117, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_123 = x_117;
} else {
 lean_dec_ref(x_117);
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
lean_object* l___private_Lean_Elab_StructInst_12__mkFieldMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_StructInst_12__mkFieldMap___closed__1;
x_10 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findIdxAux___main___at___private_Lean_Elab_StructInst_14__getFieldIdx___spec__1(x_3, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_13, 0, x_3);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l___private_Lean_Elab_StructInst_14__getFieldIdx___closed__3;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_18, 0, x_1);
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_21 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
return x_24;
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
lean_object* l___private_Lean_Elab_StructInst_14__getFieldIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_15__mkProjStx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_System_FilePath_dirName___closed__1;
x_4 = l_Lean_mkAtomFrom(x_1, x_3);
x_5 = l_Lean_mkIdentFrom(x_1, x_2);
x_6 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_7 = lean_array_push(x_6, x_1);
x_8 = lean_array_push(x_7, x_4);
x_9 = lean_array_push(x_8, x_5);
x_10 = l___private_Lean_Elab_App_23__elabAppFn___main___closed__13;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_15 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_27 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_24, x_3);
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
x_38 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_35, x_3);
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
x_55 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_52, x_3);
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
x_66 = l___private_Lean_Elab_StructInst_14__getFieldIdx(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_83 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_80, x_3);
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
lean_object* l___private_Lean_Elab_StructInst_16__mkSubstructSource___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__1;
lean_inc(x_16);
x_19 = l_List_map___main___rarg(x_18, x_16);
x_20 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_8);
lean_inc(x_15);
lean_inc(x_2);
x_21 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_2, x_3, x_15, x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_26 = l_List_head_x21___rarg(x_25, x_16);
lean_dec(x_16);
x_27 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_28 = lean_unsigned_to_nat(4u);
x_29 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_30 = l_Lean_Syntax_setArg(x_5, x_28, x_29);
x_31 = l_List_redLength___main___rarg(x_19);
x_32 = lean_mk_empty_array_with_capacity(x_31);
lean_dec(x_31);
x_33 = l_List_toArrayAux___main___rarg(x_19, x_32);
x_34 = x_33;
x_35 = l_Id_monad;
x_36 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_umapMAux___main___rarg(x_35, lean_box(0), x_36, x_37, x_34);
x_39 = x_38;
x_40 = l_Lean_List_format___rarg___closed__2;
x_41 = l_Lean_mkAtomFrom(x_5, x_40);
lean_dec(x_5);
x_42 = l_Lean_mkSepStx(x_39, x_41);
lean_dec(x_39);
x_43 = lean_unsigned_to_nat(2u);
x_44 = l_Lean_Syntax_setArg(x_30, x_43, x_42);
x_45 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_44, x_23);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_26, 1);
x_48 = lean_ctor_get(x_26, 2);
lean_dec(x_48);
x_49 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_50 = l_List_head_x21___rarg(x_49, x_47);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_26, 2, x_53);
lean_ctor_set(x_26, 1, x_52);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
x_56 = lean_ctor_get(x_26, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_57 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_58 = l_List_head_x21___rarg(x_57, x_55);
lean_dec(x_55);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_45);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_21, 0, x_62);
return x_21;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_21);
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
lean_dec(x_27);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_19);
lean_ctor_set(x_64, 3, x_23);
x_65 = lean_apply_8(x_6, x_64, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_26, 1);
x_70 = lean_ctor_get(x_26, 2);
lean_dec(x_70);
x_71 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_72 = l_List_head_x21___rarg(x_71, x_69);
lean_dec(x_69);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_68);
lean_ctor_set(x_26, 2, x_75);
lean_ctor_set(x_26, 1, x_74);
lean_ctor_set(x_65, 0, x_26);
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_26, 0);
x_78 = lean_ctor_get(x_26, 1);
x_79 = lean_ctor_get(x_26, 3);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_26);
x_80 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_81 = l_List_head_x21___rarg(x_80, x_78);
lean_dec(x_78);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_76);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_84);
lean_ctor_set(x_85, 3, x_79);
lean_ctor_set(x_65, 0, x_85);
return x_65;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_86 = lean_ctor_get(x_65, 0);
x_87 = lean_ctor_get(x_65, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_65);
x_88 = lean_ctor_get(x_26, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_26, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_26, 3);
lean_inc(x_90);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 x_91 = x_26;
} else {
 lean_dec_ref(x_26);
 x_91 = lean_box(0);
}
x_92 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_93 = l_List_head_x21___rarg(x_92, x_89);
lean_dec(x_89);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_86);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(0, 4, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_88);
lean_ctor_set(x_97, 1, x_95);
lean_ctor_set(x_97, 2, x_96);
lean_ctor_set(x_97, 3, x_90);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_87);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_26);
x_99 = !lean_is_exclusive(x_65);
if (x_99 == 0)
{
return x_65;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_65, 0);
x_101 = lean_ctor_get(x_65, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_65);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_21, 0);
x_104 = lean_ctor_get(x_21, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_21);
x_105 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__2;
x_106 = l_List_head_x21___rarg(x_105, x_16);
lean_dec(x_16);
x_107 = l_Lean_isSubobjectField_x3f(x_4, x_2, x_15);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_108 = lean_unsigned_to_nat(4u);
x_109 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_110 = l_Lean_Syntax_setArg(x_5, x_108, x_109);
x_111 = l_List_redLength___main___rarg(x_19);
x_112 = lean_mk_empty_array_with_capacity(x_111);
lean_dec(x_111);
x_113 = l_List_toArrayAux___main___rarg(x_19, x_112);
x_114 = x_113;
x_115 = l_Id_monad;
x_116 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___closed__3;
x_117 = lean_unsigned_to_nat(0u);
x_118 = l_Array_umapMAux___main___rarg(x_115, lean_box(0), x_116, x_117, x_114);
x_119 = x_118;
x_120 = l_Lean_List_format___rarg___closed__2;
x_121 = l_Lean_mkAtomFrom(x_5, x_120);
lean_dec(x_5);
x_122 = l_Lean_mkSepStx(x_119, x_121);
lean_dec(x_119);
x_123 = lean_unsigned_to_nat(2u);
x_124 = l_Lean_Syntax_setArg(x_110, x_123, x_122);
x_125 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_124, x_103);
x_126 = lean_ctor_get(x_106, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_106, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_106, 3);
lean_inc(x_128);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_129 = x_106;
} else {
 lean_dec_ref(x_106);
 x_129 = lean_box(0);
}
x_130 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_131 = l_List_head_x21___rarg(x_130, x_127);
lean_dec(x_127);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_134, 0, x_125);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(0, 4, 0);
} else {
 x_135 = x_129;
}
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_128);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_104);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_107, 0);
lean_inc(x_137);
lean_dec(x_107);
x_138 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_19);
lean_ctor_set(x_138, 3, x_103);
x_139 = lean_apply_8(x_6, x_138, x_8, x_9, x_10, x_11, x_12, x_13, x_104);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_ctor_get(x_106, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_106, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_106, 3);
lean_inc(x_145);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_146 = x_106;
} else {
 lean_dec_ref(x_106);
 x_146 = lean_box(0);
}
x_147 = l_Lean_Elab_Term_StructInst_FieldLHS_inhabited;
x_148 = l_List_head_x21___rarg(x_147, x_144);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_140);
if (lean_is_scalar(x_146)) {
 x_152 = lean_alloc_ctor(0, 4, 0);
} else {
 x_152 = x_146;
}
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_151);
lean_ctor_set(x_152, 3, x_145);
if (lean_is_scalar(x_142)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_142;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_141);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_106);
x_154 = lean_ctor_get(x_139, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_139, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_156 = x_139;
} else {
 lean_dec_ref(x_139);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
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
x_158 = !lean_is_exclusive(x_21);
if (x_158 == 0)
{
return x_21;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_21, 0);
x_160 = lean_ctor_get(x_21, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_21);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; 
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
x_162 = lean_ctor_get(x_17, 0);
lean_inc(x_162);
lean_dec(x_17);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_14);
return x_163;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_16 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed), 14, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
x_20 = l_Std_HashMap_toList___rarg(x_17);
lean_dec(x_17);
x_21 = l_List_mapM___main___rarg(x_7, lean_box(0), lean_box(0), x_19, x_20);
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_inc(x_16);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___lambda__4), 15, 7);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_7, 3, x_23);
x_24 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_25 = lean_apply_7(x_24, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
x_28 = lean_ctor_get(x_7, 2);
x_29 = lean_ctor_get(x_7, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_16, x_29);
lean_dec(x_16);
x_31 = l_Lean_replaceRef(x_30, x_29);
lean_dec(x_30);
x_32 = l_Lean_replaceRef(x_31, x_29);
lean_dec(x_29);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_27);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
x_34 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___rarg(x_17, x_2, x_18);
x_35 = lean_apply_7(x_34, x_3, x_4, x_5, x_6, x_33, x_8, x_12);
return x_35;
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_StructInst_17__groupFields___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
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
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_9);
x_19 = l_Lean_Elab_Term_StructInst_findField_x3f(x_18, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
lean_inc(x_9);
lean_inc(x_3);
x_20 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_9);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
x_21 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_box(2);
lean_inc(x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_10);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_17);
return x_28;
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_21);
x_29 = l_Lean_mkHole(x_4);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_9);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_30);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_10);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_17);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_21, 0);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_Syntax_getArg(x_37, x_38);
lean_dec(x_37);
lean_inc(x_9);
x_40 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_39, x_9);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_inc(x_4);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_9);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_5);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_44);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_10);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_20, 0);
lean_inc(x_48);
lean_dec(x_20);
x_49 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_9);
x_50 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_6, x_9, x_49, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_5);
lean_inc(x_4);
x_53 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_53, 0, x_4);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_5);
lean_ctor_set(x_53, 3, x_51);
x_54 = lean_apply_8(x_7, x_53, x_11, x_12, x_13, x_14, x_15, x_16, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_inc(x_4);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_4);
lean_ctor_set(x_58, 1, x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_5);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_57);
lean_ctor_set(x_61, 3, x_60);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_10);
lean_ctor_set(x_54, 0, x_62);
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_63);
lean_inc(x_4);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_9);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_5);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_65);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_10);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_54);
if (x_72 == 0)
{
return x_54;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_54, 0);
x_74 = lean_ctor_get(x_54, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_54);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_48);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_76 = !lean_is_exclusive(x_50);
if (x_76 == 0)
{
return x_50;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_50, 0);
x_78 = lean_ctor_get(x_50, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_50);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_19, 0);
lean_inc(x_80);
lean_dec(x_19);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_10);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_17);
return x_82;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_17 = lean_box(0);
lean_inc(x_15);
lean_inc(x_16);
lean_inc(x_2);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed), 17, 7);
lean_closure_set(x_18, 0, x_2);
lean_closure_set(x_18, 1, x_13);
lean_closure_set(x_18, 2, x_14);
lean_closure_set(x_18, 3, x_16);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_15);
lean_closure_set(x_18, 6, x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_7, 3);
x_21 = l_Lean_replaceRef(x_16, x_20);
lean_dec(x_16);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_7, 3, x_23);
x_24 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_iterateMAux___main___rarg(x_24, lean_box(0), x_15, x_18, x_25, x_17);
x_27 = lean_apply_7(x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = l_List_reverse___rarg(x_29);
x_31 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = l_List_reverse___rarg(x_32);
x_35 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_2);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 2);
x_44 = lean_ctor_get(x_7, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_45 = l_Lean_replaceRef(x_16, x_44);
lean_dec(x_16);
x_46 = l_Lean_replaceRef(x_45, x_44);
lean_dec(x_45);
x_47 = l_Lean_replaceRef(x_46, x_44);
lean_dec(x_44);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set(x_48, 2, x_43);
lean_ctor_set(x_48, 3, x_47);
x_49 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_iterateMAux___main___rarg(x_49, lean_box(0), x_15, x_18, x_50, x_17);
x_52 = lean_apply_7(x_51, x_3, x_4, x_5, x_6, x_48, x_8, x_12);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
x_56 = l_List_reverse___rarg(x_53);
x_57 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_2, x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_2);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_61 = x_52;
} else {
 lean_dec_ref(x_52);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l___private_Lean_Elab_StructInst_18__addMissingFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_18;
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_21 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_20);
x_22 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_20);
x_23 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_19);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_19, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_20);
lean_dec(x_20);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_31 = l_Lean_Syntax_setArg(x_5, x_29, x_30);
x_32 = l_List_redLength___main___rarg(x_22);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___main___rarg(x_22, x_33);
x_35 = x_34;
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_36, x_35);
x_38 = x_37;
x_39 = l_Lean_List_format___rarg___closed__2;
x_40 = l_Lean_mkAtomFrom(x_5, x_39);
x_41 = l_Lean_mkSepStx(x_38, x_40);
lean_dec(x_38);
x_42 = lean_unsigned_to_nat(2u);
x_43 = l_Lean_Syntax_setArg(x_31, x_42, x_41);
x_44 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_43, x_25);
x_45 = !lean_is_exclusive(x_27);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_27, 1);
x_47 = lean_ctor_get(x_27, 2);
lean_dec(x_47);
x_48 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_46);
lean_dec(x_46);
x_49 = lean_box(0);
lean_ctor_set(x_6, 1, x_49);
lean_ctor_set(x_6, 0, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_27, 2, x_50);
lean_ctor_set(x_27, 1, x_6);
x_51 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_27);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_27);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_27);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
x_65 = lean_ctor_get(x_27, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
x_66 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_64);
lean_dec(x_64);
x_67 = lean_box(0);
lean_ctor_set(x_6, 1, x_67);
lean_ctor_set(x_6, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_44);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_6);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_65);
x_70 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_71);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_69);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_78 = x_70;
} else {
 lean_dec_ref(x_70);
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
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_28, 0);
lean_inc(x_80);
lean_dec(x_28);
lean_inc(x_5);
x_81 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_81, 0, x_5);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set(x_81, 2, x_22);
lean_ctor_set(x_81, 3, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_82 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_81, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = !lean_is_exclusive(x_27);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_27, 1);
x_87 = lean_ctor_get(x_27, 2);
lean_dec(x_87);
x_88 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_86);
lean_dec(x_86);
x_89 = lean_box(0);
lean_ctor_set(x_6, 1, x_89);
lean_ctor_set(x_6, 0, x_88);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_27, 2, x_90);
lean_ctor_set(x_27, 1, x_6);
x_91 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_27);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_91, 0);
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_91);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_27);
lean_ctor_set(x_97, 1, x_95);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_27);
x_99 = !lean_is_exclusive(x_91);
if (x_99 == 0)
{
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_91, 0);
x_101 = lean_ctor_get(x_91, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_91);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_103 = lean_ctor_get(x_27, 0);
x_104 = lean_ctor_get(x_27, 1);
x_105 = lean_ctor_get(x_27, 3);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_27);
x_106 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_104);
lean_dec(x_104);
x_107 = lean_box(0);
lean_ctor_set(x_6, 1, x_107);
lean_ctor_set(x_6, 0, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_83);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_103);
lean_ctor_set(x_109, 1, x_6);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_105);
x_110 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_84);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_109);
lean_ctor_set(x_114, 1, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_109);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
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
x_120 = !lean_is_exclusive(x_82);
if (x_120 == 0)
{
return x_82;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_82, 0);
x_122 = lean_ctor_get(x_82, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_82);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
uint8_t x_124; 
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
x_124 = !lean_is_exclusive(x_24);
if (x_124 == 0)
{
return x_24;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_24, 0);
x_126 = lean_ctor_get(x_24, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_24);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_20);
lean_dec(x_19);
x_128 = lean_ctor_get(x_21, 0);
lean_inc(x_128);
lean_dec(x_21);
x_129 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set(x_6, 1, x_131);
lean_ctor_set(x_6, 0, x_128);
lean_ctor_set(x_129, 0, x_6);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set(x_6, 1, x_132);
lean_ctor_set(x_6, 0, x_128);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_6);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
uint8_t x_135; 
lean_dec(x_128);
lean_free_object(x_6);
x_135 = !lean_is_exclusive(x_129);
if (x_135 == 0)
{
return x_129;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_129, 0);
x_137 = lean_ctor_get(x_129, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_129);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_139 = lean_ctor_get(x_6, 0);
x_140 = lean_ctor_get(x_6, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_6);
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = l___private_Lean_Elab_StructInst_13__isSimpleField_x3f(x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_inc(x_142);
x_144 = l_List_map___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__2(x_142);
x_145 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_7);
lean_inc(x_141);
lean_inc(x_3);
x_146 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_3, x_4, x_141, x_145, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__3(x_142);
lean_dec(x_142);
lean_inc(x_3);
lean_inc(x_2);
x_150 = l_Lean_isSubobjectField_x3f(x_2, x_3, x_141);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_151 = lean_unsigned_to_nat(4u);
x_152 = l_Lean_mkOptionalNode___closed__1;
lean_inc(x_5);
x_153 = l_Lean_Syntax_setArg(x_5, x_151, x_152);
x_154 = l_List_redLength___main___rarg(x_144);
x_155 = lean_mk_empty_array_with_capacity(x_154);
lean_dec(x_154);
x_156 = l_List_toArrayAux___main___rarg(x_144, x_155);
x_157 = x_156;
x_158 = lean_unsigned_to_nat(0u);
x_159 = l_Array_umapMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__4(x_158, x_157);
x_160 = x_159;
x_161 = l_Lean_List_format___rarg___closed__2;
x_162 = l_Lean_mkAtomFrom(x_5, x_161);
x_163 = l_Lean_mkSepStx(x_160, x_162);
lean_dec(x_160);
x_164 = lean_unsigned_to_nat(2u);
x_165 = l_Lean_Syntax_setArg(x_153, x_164, x_163);
x_166 = l_Lean_Elab_Term_StructInst_setStructSourceSyntax(x_165, x_147);
x_167 = lean_ctor_get(x_149, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_149, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_149, 3);
lean_inc(x_169);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_170 = x_149;
} else {
 lean_dec_ref(x_149);
 x_170 = lean_box(0);
}
x_171 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_168);
lean_dec(x_168);
x_172 = lean_box(0);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_166);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 4, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_174);
lean_ctor_set(x_175, 3, x_169);
x_176 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
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
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_175);
lean_ctor_set(x_180, 1, x_177);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_175);
x_182 = lean_ctor_get(x_176, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_150, 0);
lean_inc(x_186);
lean_dec(x_150);
lean_inc(x_5);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_5);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_187, 2, x_144);
lean_ctor_set(x_187, 3, x_147);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_188 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_187, x_7, x_8, x_9, x_10, x_11, x_12, x_148);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_149, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_149, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_149, 3);
lean_inc(x_193);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 lean_ctor_release(x_149, 2);
 lean_ctor_release(x_149, 3);
 x_194 = x_149;
} else {
 lean_dec_ref(x_149);
 x_194 = lean_box(0);
}
x_195 = l_List_head_x21___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__5(x_192);
lean_dec(x_192);
x_196 = lean_box(0);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_189);
if (lean_is_scalar(x_194)) {
 x_199 = lean_alloc_ctor(0, 4, 0);
} else {
 x_199 = x_194;
}
lean_ctor_set(x_199, 0, x_191);
lean_ctor_set(x_199, 1, x_197);
lean_ctor_set(x_199, 2, x_198);
lean_ctor_set(x_199, 3, x_193);
x_200 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_190);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_203 = x_200;
} else {
 lean_dec_ref(x_200);
 x_203 = lean_box(0);
}
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_201);
if (lean_is_scalar(x_203)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_203;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_199);
x_206 = lean_ctor_get(x_200, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_200, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_208 = x_200;
} else {
 lean_dec_ref(x_200);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_149);
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_210 = lean_ctor_get(x_188, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_212 = x_188;
} else {
 lean_dec_ref(x_188);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_146, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_146, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_216 = x_146;
} else {
 lean_dec_ref(x_146);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_142);
lean_dec(x_141);
x_218 = lean_ctor_get(x_143, 0);
lean_inc(x_218);
lean_dec(x_143);
x_219 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_140, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_222 = x_219;
} else {
 lean_dec_ref(x_219);
 x_222 = lean_box(0);
}
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_220);
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_222;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_218);
x_225 = lean_ctor_get(x_219, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_219, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_227 = x_219;
} else {
 lean_dec_ref(x_219);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_StructInst_12__mkFieldMap(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Std_HashMap_toList___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__6(x_15);
lean_dec(x_15);
x_18 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
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
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed), 13, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_6, 3, x_21);
x_22 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_ctor_get(x_6, 2);
x_26 = lean_ctor_get(x_6, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_27 = l_Lean_replaceRef(x_15, x_26);
lean_dec(x_15);
x_28 = l_Lean_replaceRef(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_replaceRef(x_28, x_26);
lean_dec(x_26);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_29);
x_31 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at___private_Lean_Elab_StructInst_9__expandNumLitFields___spec__2(x_1, x_16, x_2, x_3, x_4, x_5, x_30, x_7, x_11);
return x_31;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_array_get_size(x_8);
x_19 = lean_nat_dec_lt(x_9, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_array_fget(x_8, x_9);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_9, x_22);
lean_dec(x_9);
x_24 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
lean_inc(x_21);
x_25 = l_Lean_Elab_Term_StructInst_findField_x3f(x_24, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_inc(x_21);
lean_inc(x_4);
lean_inc(x_3);
x_26 = l_Lean_isSubobjectField_x3f(x_3, x_4, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_box(2);
lean_inc(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_21);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
lean_inc(x_6);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_6);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
x_9 = x_23;
x_10 = x_34;
goto _start;
}
case 1:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_27);
x_36 = l_Lean_mkHole(x_6);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_21);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
lean_inc(x_6);
x_42 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_10);
x_9 = x_23;
x_10 = x_43;
goto _start;
}
default: 
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_27, 0);
lean_inc(x_45);
lean_dec(x_27);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Lean_Syntax_getArg(x_45, x_46);
lean_dec(x_45);
lean_inc(x_21);
x_48 = l___private_Lean_Elab_StructInst_15__mkProjStx(x_47, x_21);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_inc(x_6);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_21);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
lean_inc(x_6);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_52);
lean_ctor_set(x_54, 2, x_49);
lean_ctor_set(x_54, 3, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_10);
x_9 = x_23;
x_10 = x_55;
goto _start;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_26, 0);
lean_inc(x_57);
lean_dec(x_26);
x_58 = l_Lean_Elab_Term_StructInst_Struct_source(x_1);
lean_inc(x_11);
lean_inc(x_21);
lean_inc(x_4);
x_59 = l___private_Lean_Elab_StructInst_16__mkSubstructSource(x_4, x_5, x_21, x_58, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_7);
lean_inc(x_6);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_6);
lean_ctor_set(x_62, 1, x_57);
lean_ctor_set(x_62, 2, x_7);
lean_ctor_set(x_62, 3, x_60);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_62, x_11, x_12, x_13, x_14, x_15, x_16, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_64);
lean_inc(x_6);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_6);
lean_ctor_set(x_67, 1, x_21);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
lean_inc(x_6);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_6);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_10);
x_9 = x_23;
x_10 = x_72;
x_17 = x_65;
goto _start;
}
else
{
uint8_t x_74; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_63);
if (x_74 == 0)
{
return x_63;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_63, 0);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_63);
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
lean_dec(x_57);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_59);
if (x_78 == 0)
{
return x_59;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_59, 0);
x_80 = lean_ctor_get(x_59, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_59);
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
lean_object* x_82; lean_object* x_83; 
lean_dec(x_21);
x_82 = lean_ctor_get(x_25, 0);
lean_inc(x_82);
lean_dec(x_25);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_10);
x_9 = x_23;
x_10 = x_83;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_13 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Lean_getStructureFields(x_12, x_13);
x_15 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_16 = lean_box(0);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_6, 3, x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_14, x_22, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
lean_dec(x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_List_reverse___rarg(x_25);
x_27 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = l_List_reverse___rarg(x_28);
x_31 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
x_39 = lean_ctor_get(x_6, 2);
x_40 = lean_ctor_get(x_6, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_41 = l_Lean_replaceRef(x_15, x_40);
x_42 = l_Lean_replaceRef(x_41, x_40);
lean_dec(x_41);
x_43 = l_Lean_replaceRef(x_42, x_40);
lean_dec(x_40);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_39);
lean_ctor_set(x_44, 3, x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_10, x_12, x_13, x_14, x_15, x_16, x_14, x_45, x_16, x_2, x_3, x_4, x_5, x_44, x_7, x_11);
lean_dec(x_14);
lean_dec(x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_List_reverse___rarg(x_47);
x_51 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_55 = x_46;
} else {
 lean_dec_ref(x_46);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l___private_Lean_Elab_StructInst_8__expandCompositeFields___closed__1;
x_10 = l_Lean_Elab_Term_StructInst_Struct_modifyFieldsM___at_Lean_Elab_Term_StructInst_Struct_modifyFields___spec__1(x_1, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_9__expandNumLitFields(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
x_14 = l___private_Lean_Elab_StructInst_10__expandParentFields(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
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
x_17 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_StructInst_18__addMissingFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__10(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_mapM___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_StructInst_17__groupFields___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Array_iterateMAux___main___at___private_Lean_Elab_StructInst_19__expandStruct___main___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
lean_object* l___private_Lean_Elab_StructInst_19__expandStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
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
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_16 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint8_t x_33; lean_object* x_34; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_17, sizeof(void*)*3);
lean_dec(x_17);
x_33 = (uint8_t)((x_21 << 24) >> 61);
x_34 = lean_box(x_33);
if (lean_obj_tag(x_34) == 3)
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_19);
x_36 = 1;
x_37 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_38 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_35, x_36, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_expr_instantiate1(x_20, x_39);
lean_dec(x_20);
lean_inc(x_39);
x_42 = l_Lean_mkApp(x_3, x_39);
x_43 = l_Lean_Expr_mvarId_x21(x_39);
lean_dec(x_39);
x_44 = lean_array_push(x_4, x_43);
x_1 = x_15;
x_2 = x_41;
x_3 = x_42;
x_4 = x_44;
x_11 = x_40;
goto _start;
}
else
{
lean_object* x_46; 
lean_dec(x_34);
x_46 = lean_box(0);
x_22 = x_46;
goto block_32;
}
block_32:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_24 = 0;
x_25 = lean_box(0);
lean_inc(x_7);
lean_inc(x_5);
x_26 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_23, x_24, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_expr_instantiate1(x_20, x_27);
lean_dec(x_20);
x_30 = l_Lean_mkApp(x_3, x_27);
x_1 = x_15;
x_2 = x_29;
x_3 = x_30;
x_11 = x_28;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_16);
if (x_50 == 0)
{
return x_16;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_16, 0);
x_52 = lean_ctor_get(x_16, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_2);
lean_ctor_set(x_54, 2, x_4);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_11);
return x_55;
}
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_6);
return x_12;
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
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
x_14 = l___private_Lean_Elab_StructInst_21__getForallBody___main(x_2, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
x_19 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_13, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_4);
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
lean_object* l___private_Lean_Elab_StructInst_22__propagateExpectedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
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
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
lean_inc(x_2);
x_14 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
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
lean_inc(x_2);
x_24 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
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
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_21 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main(x_19, x_18, x_16, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
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
lean_inc(x_3);
x_26 = l___private_Lean_Elab_StructInst_22__propagateExpectedType(x_24, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_forMAux___main___at_Lean_Elab_Term_synthesizeAppInstMVars___spec__1(x_28, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_28);
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
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_21);
if (x_43 == 0)
{
return x_21;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_21, 0);
x_45 = lean_ctor_get(x_21, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_21);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_StructInst_23__mkCtorHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
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
lean_object* l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg___closed__6;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__2;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
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
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_7, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_14, 2);
lean_dec(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_14, 2, x_18);
x_19 = lean_st_ref_set(x_7, x_14, x_15);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = l_Lean_TraceState_Inhabited___closed__1;
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_st_ref_set(x_7, x_39, x_15);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_SynthInstance_8__synthInstanceImp_x3f(x_1, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_50);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_53 = x_51;
} else {
 lean_dec_ref(x_51);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_allDefault___main(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_synthInstance_x3f___at_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_24; lean_object* x_29; lean_object* x_30; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
x_24 = x_31;
goto block_28;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 2);
x_43 = lean_ctor_get(x_13, 3);
lean_dec(x_43);
x_44 = lean_ctor_get(x_13, 1);
lean_dec(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_46 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 7)
{
lean_dec(x_45);
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_47, 2);
lean_inc(x_64);
lean_dec(x_47);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_63);
x_67 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_68 = l_Lean_Elab_Term_elabTermEnsuringType(x_65, x_66, x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = l_Lean_mkApp(x_35, x_70);
x_72 = lean_expr_instantiate1(x_64, x_70);
lean_dec(x_64);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_13, 3, x_73);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_72);
lean_ctor_set(x_2, 0, x_71);
lean_ctor_set(x_68, 0, x_2);
x_15 = x_68;
goto block_23;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_68, 0);
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_68);
lean_inc(x_74);
x_76 = l_Lean_mkApp(x_35, x_74);
x_77 = lean_expr_instantiate1(x_64, x_74);
lean_dec(x_64);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_13, 3, x_78);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_77);
lean_ctor_set(x_2, 0, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_2);
lean_ctor_set(x_79, 1, x_75);
x_15 = x_79;
goto block_23;
}
}
else
{
uint8_t x_80; 
lean_dec(x_64);
lean_free_object(x_13);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_80 = !lean_is_exclusive(x_68);
if (x_80 == 0)
{
x_15 = x_68;
goto block_23;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_68, 0);
x_82 = lean_ctor_get(x_68, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_68);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_15 = x_83;
goto block_23;
}
}
}
case 1:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_47, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_47, 2);
lean_inc(x_85);
lean_dec(x_47);
x_86 = !lean_is_exclusive(x_42);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_42, 0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_84);
x_88 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_87, x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_2);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_91);
x_92 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_87, x_91, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_93, 0);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_98 = l_Lean_Elab_Term_ensureHasType(x_91, x_96, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_98, 0);
lean_ctor_set(x_42, 0, x_97);
lean_inc(x_100);
x_101 = l_Lean_mkApp(x_35, x_100);
x_102 = lean_expr_instantiate1(x_85, x_100);
lean_dec(x_85);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_13, 3, x_103);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 0, x_102);
lean_ctor_set(x_29, 1, x_93);
lean_ctor_set(x_29, 0, x_101);
lean_ctor_set(x_98, 0, x_29);
x_15 = x_98;
goto block_23;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
lean_ctor_set(x_42, 0, x_97);
lean_inc(x_104);
x_106 = l_Lean_mkApp(x_35, x_104);
x_107 = lean_expr_instantiate1(x_85, x_104);
lean_dec(x_85);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_13, 3, x_108);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_93, 1, x_3);
lean_ctor_set(x_93, 0, x_107);
lean_ctor_set(x_29, 1, x_93);
lean_ctor_set(x_29, 0, x_106);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_29);
lean_ctor_set(x_109, 1, x_105);
x_15 = x_109;
goto block_23;
}
}
else
{
uint8_t x_110; 
lean_free_object(x_93);
lean_dec(x_97);
lean_free_object(x_42);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_110 = !lean_is_exclusive(x_98);
if (x_110 == 0)
{
x_15 = x_98;
goto block_23;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_98, 0);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_98);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_15 = x_113;
goto block_23;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_93, 0);
x_115 = lean_ctor_get(x_93, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_93);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_116 = l_Lean_Elab_Term_ensureHasType(x_91, x_114, x_4, x_5, x_6, x_7, x_8, x_9, x_94);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
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
lean_ctor_set(x_42, 0, x_115);
lean_inc(x_117);
x_120 = l_Lean_mkApp(x_35, x_117);
x_121 = lean_expr_instantiate1(x_85, x_117);
lean_dec(x_85);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_13, 3, x_122);
lean_ctor_set(x_3, 1, x_40);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_3);
lean_ctor_set(x_29, 1, x_123);
lean_ctor_set(x_29, 0, x_120);
if (lean_is_scalar(x_119)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_119;
}
lean_ctor_set(x_124, 0, x_29);
lean_ctor_set(x_124, 1, x_118);
x_15 = x_124;
goto block_23;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_115);
lean_free_object(x_42);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
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
x_15 = x_128;
goto block_23;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_91);
lean_free_object(x_42);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_129 = !lean_is_exclusive(x_92);
if (x_129 == 0)
{
x_15 = x_92;
goto block_23;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_92, 0);
x_131 = lean_ctor_get(x_92, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_92);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_15 = x_132;
goto block_23;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_87);
lean_dec(x_84);
x_133 = !lean_is_exclusive(x_88);
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_ctor_get(x_88, 0);
lean_dec(x_134);
x_135 = !lean_is_exclusive(x_89);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_89, 0);
x_137 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_137);
lean_inc(x_136);
x_138 = l_Lean_mkApp(x_35, x_136);
x_139 = lean_expr_instantiate1(x_85, x_136);
lean_dec(x_85);
lean_ctor_set(x_13, 3, x_89);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_139);
lean_ctor_set(x_2, 0, x_138);
lean_ctor_set(x_88, 0, x_2);
x_15 = x_88;
goto block_23;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_89, 0);
lean_inc(x_140);
lean_dec(x_89);
x_141 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_141);
lean_inc(x_140);
x_142 = l_Lean_mkApp(x_35, x_140);
x_143 = lean_expr_instantiate1(x_85, x_140);
lean_dec(x_85);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_13, 3, x_144);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_143);
lean_ctor_set(x_2, 0, x_142);
lean_ctor_set(x_88, 0, x_2);
x_15 = x_88;
goto block_23;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_88, 1);
lean_inc(x_145);
lean_dec(x_88);
x_146 = lean_ctor_get(x_89, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_147 = x_89;
} else {
 lean_dec_ref(x_89);
 x_147 = lean_box(0);
}
x_148 = l_Lean_mkHole(x_41);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_148);
lean_inc(x_146);
x_149 = l_Lean_mkApp(x_35, x_146);
x_150 = lean_expr_instantiate1(x_85, x_146);
lean_dec(x_85);
if (lean_is_scalar(x_147)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_147;
}
lean_ctor_set(x_151, 0, x_146);
lean_ctor_set(x_13, 3, x_151);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_150);
lean_ctor_set(x_2, 0, x_149);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_2);
lean_ctor_set(x_152, 1, x_145);
x_15 = x_152;
goto block_23;
}
}
}
else
{
uint8_t x_153; 
lean_free_object(x_42);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_153 = !lean_is_exclusive(x_88);
if (x_153 == 0)
{
x_15 = x_88;
goto block_23;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_88, 0);
x_155 = lean_ctor_get(x_88, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_88);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_15 = x_156;
goto block_23;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_42, 0);
lean_inc(x_157);
lean_dec(x_42);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_84);
x_158 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_157, x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_48);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_free_object(x_2);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_84);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_161);
x_162 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_157, x_161, x_4, x_5, x_6, x_7, x_8, x_9, x_160);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_167 = x_163;
} else {
 lean_dec_ref(x_163);
 x_167 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_168 = l_Lean_Elab_Term_ensureHasType(x_161, x_165, x_4, x_5, x_6, x_7, x_8, x_9, x_164);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_166);
lean_inc(x_169);
x_173 = l_Lean_mkApp(x_35, x_169);
x_174 = lean_expr_instantiate1(x_85, x_169);
lean_dec(x_85);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_13, 3, x_175);
lean_ctor_set(x_13, 2, x_172);
lean_ctor_set(x_3, 1, x_40);
if (lean_is_scalar(x_167)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_167;
}
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_3);
lean_ctor_set(x_29, 1, x_176);
lean_ctor_set(x_29, 0, x_173);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_171;
}
lean_ctor_set(x_177, 0, x_29);
lean_ctor_set(x_177, 1, x_170);
x_15 = x_177;
goto block_23;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_178 = lean_ctor_get(x_168, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_180 = x_168;
} else {
 lean_dec_ref(x_168);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
x_15 = x_181;
goto block_23;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_161);
lean_dec(x_85);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_182 = lean_ctor_get(x_162, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_162, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_184 = x_162;
} else {
 lean_dec_ref(x_162);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_15 = x_185;
goto block_23;
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_157);
lean_dec(x_84);
x_186 = lean_ctor_get(x_158, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_187 = x_158;
} else {
 lean_dec_ref(x_158);
 x_187 = lean_box(0);
}
x_188 = lean_ctor_get(x_159, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 x_189 = x_159;
} else {
 lean_dec_ref(x_159);
 x_189 = lean_box(0);
}
x_190 = l_Lean_mkHole(x_41);
x_191 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_191, 0, x_190);
lean_inc(x_188);
x_192 = l_Lean_mkApp(x_35, x_188);
x_193 = lean_expr_instantiate1(x_85, x_188);
lean_dec(x_85);
if (lean_is_scalar(x_189)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_189;
}
lean_ctor_set(x_194, 0, x_188);
lean_ctor_set(x_13, 3, x_194);
lean_ctor_set(x_13, 2, x_191);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_193);
lean_ctor_set(x_2, 0, x_192);
if (lean_is_scalar(x_187)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_187;
}
lean_ctor_set(x_195, 0, x_2);
lean_ctor_set(x_195, 1, x_186);
x_15 = x_195;
goto block_23;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_157);
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_13);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_196 = lean_ctor_get(x_158, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_158, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_198 = x_158;
} else {
 lean_dec_ref(x_158);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
x_15 = x_199;
goto block_23;
}
}
}
default: 
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_200 = lean_ctor_get(x_47, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_47, 2);
lean_inc(x_201);
lean_dec(x_47);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_200);
x_203 = lean_ctor_get(x_8, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_8, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_8, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_8, 3);
lean_inc(x_206);
x_207 = l_Lean_replaceRef(x_41, x_206);
x_208 = l_Lean_replaceRef(x_207, x_206);
lean_dec(x_207);
x_209 = l_Lean_replaceRef(x_208, x_206);
lean_dec(x_206);
lean_dec(x_208);
x_210 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_210, 0, x_203);
lean_ctor_set(x_210, 1, x_204);
lean_ctor_set(x_210, 2, x_205);
lean_ctor_set(x_210, 3, x_209);
x_211 = 0;
x_212 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_213 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_202, x_211, x_212, x_4, x_5, x_6, x_7, x_210, x_9, x_48);
lean_dec(x_210);
x_214 = !lean_is_exclusive(x_213);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_213, 0);
x_216 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_215);
lean_inc(x_216);
x_217 = l_Lean_mkApp(x_35, x_216);
x_218 = lean_expr_instantiate1(x_201, x_216);
lean_dec(x_201);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_13, 3, x_219);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_218);
lean_ctor_set(x_2, 0, x_217);
lean_ctor_set(x_213, 0, x_2);
x_15 = x_213;
goto block_23;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_ctor_get(x_213, 0);
x_221 = lean_ctor_get(x_213, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_213);
x_222 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_220);
lean_inc(x_222);
x_223 = l_Lean_mkApp(x_35, x_222);
x_224 = lean_expr_instantiate1(x_201, x_222);
lean_dec(x_201);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_13, 3, x_225);
lean_ctor_set(x_3, 1, x_40);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_224);
lean_ctor_set(x_2, 0, x_223);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_2);
lean_ctor_set(x_226, 1, x_221);
x_15 = x_226;
goto block_23;
}
}
}
}
else
{
lean_object* x_227; 
lean_free_object(x_13);
lean_dec(x_42);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_227 = lean_box(0);
x_49 = x_227;
goto block_62;
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
x_50 = l_Lean_indentExpr(x_47);
x_51 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_52 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_ctor_get(x_8, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_8, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_8, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_8, 3);
lean_inc(x_56);
x_57 = l_Lean_replaceRef(x_41, x_56);
lean_dec(x_41);
x_58 = l_Lean_replaceRef(x_57, x_56);
lean_dec(x_57);
x_59 = l_Lean_replaceRef(x_58, x_56);
lean_dec(x_56);
lean_dec(x_58);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_54);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_59);
lean_inc(x_4);
lean_inc(x_1);
x_61 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_45, x_1, x_52, x_4, x_5, x_6, x_7, x_60, x_9, x_48);
lean_dec(x_60);
x_15 = x_61;
goto block_23;
}
}
else
{
uint8_t x_228; 
lean_dec(x_45);
lean_free_object(x_13);
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_29);
lean_dec(x_40);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_228 = !lean_is_exclusive(x_46);
if (x_228 == 0)
{
x_15 = x_46;
goto block_23;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_46, 0);
x_230 = lean_ctor_get(x_46, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_46);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_15 = x_231;
goto block_23;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_ctor_get(x_29, 0);
x_233 = lean_ctor_get(x_29, 1);
x_234 = lean_ctor_get(x_13, 0);
x_235 = lean_ctor_get(x_13, 2);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_13);
x_236 = lean_ctor_get(x_32, 1);
lean_inc(x_236);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_237 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_232, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
if (lean_obj_tag(x_238) == 7)
{
lean_dec(x_236);
switch (lean_obj_tag(x_235)) {
case 0:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_238, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_238, 2);
lean_inc(x_255);
lean_dec(x_238);
x_256 = lean_ctor_get(x_235, 0);
lean_inc(x_256);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_254);
x_258 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_259 = l_Lean_Elab_Term_elabTermEnsuringType(x_256, x_257, x_258, x_4, x_5, x_6, x_7, x_8, x_9, x_239);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_262 = x_259;
} else {
 lean_dec_ref(x_259);
 x_262 = lean_box(0);
}
lean_inc(x_260);
x_263 = l_Lean_mkApp(x_35, x_260);
x_264 = lean_expr_instantiate1(x_255, x_260);
lean_dec(x_255);
x_265 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_265, 0, x_260);
x_266 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_266, 0, x_234);
lean_ctor_set(x_266, 1, x_30);
lean_ctor_set(x_266, 2, x_235);
lean_ctor_set(x_266, 3, x_265);
lean_ctor_set(x_3, 1, x_233);
lean_ctor_set(x_3, 0, x_266);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_264);
lean_ctor_set(x_2, 0, x_263);
if (lean_is_scalar(x_262)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_262;
}
lean_ctor_set(x_267, 0, x_2);
lean_ctor_set(x_267, 1, x_261);
x_15 = x_267;
goto block_23;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_255);
lean_dec(x_235);
lean_dec(x_234);
lean_free_object(x_29);
lean_dec(x_233);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_268 = lean_ctor_get(x_259, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_259, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_270 = x_259;
} else {
 lean_dec_ref(x_259);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
x_15 = x_271;
goto block_23;
}
}
case 1:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_ctor_get(x_238, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_238, 2);
lean_inc(x_273);
lean_dec(x_238);
x_274 = lean_ctor_get(x_235, 0);
lean_inc(x_274);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 x_275 = x_235;
} else {
 lean_dec_ref(x_235);
 x_275 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_272);
x_276 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_274, x_272, x_4, x_5, x_6, x_7, x_8, x_9, x_239);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_free_object(x_2);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_272);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_279);
x_280 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_274, x_279, x_4, x_5, x_6, x_7, x_8, x_9, x_278);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
x_283 = lean_ctor_get(x_281, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_281)) {
 lean_ctor_release(x_281, 0);
 lean_ctor_release(x_281, 1);
 x_285 = x_281;
} else {
 lean_dec_ref(x_281);
 x_285 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_286 = l_Lean_Elab_Term_ensureHasType(x_279, x_283, x_4, x_5, x_6, x_7, x_8, x_9, x_282);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_290 = lean_alloc_ctor(1, 1, 0);
} else {
 x_290 = x_275;
}
lean_ctor_set(x_290, 0, x_284);
lean_inc(x_287);
x_291 = l_Lean_mkApp(x_35, x_287);
x_292 = lean_expr_instantiate1(x_273, x_287);
lean_dec(x_273);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_287);
x_294 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_294, 0, x_234);
lean_ctor_set(x_294, 1, x_30);
lean_ctor_set(x_294, 2, x_290);
lean_ctor_set(x_294, 3, x_293);
lean_ctor_set(x_3, 1, x_233);
lean_ctor_set(x_3, 0, x_294);
if (lean_is_scalar(x_285)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_285;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_3);
lean_ctor_set(x_29, 1, x_295);
lean_ctor_set(x_29, 0, x_291);
if (lean_is_scalar(x_289)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_289;
}
lean_ctor_set(x_296, 0, x_29);
lean_ctor_set(x_296, 1, x_288);
x_15 = x_296;
goto block_23;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_234);
lean_free_object(x_29);
lean_dec(x_233);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_297 = lean_ctor_get(x_286, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_286, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_299 = x_286;
} else {
 lean_dec_ref(x_286);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
x_15 = x_300;
goto block_23;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_279);
lean_dec(x_275);
lean_dec(x_273);
lean_dec(x_234);
lean_free_object(x_29);
lean_dec(x_233);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_301 = lean_ctor_get(x_280, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_280, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_303 = x_280;
} else {
 lean_dec_ref(x_280);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
x_15 = x_304;
goto block_23;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_274);
lean_dec(x_272);
x_305 = lean_ctor_get(x_276, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_306 = x_276;
} else {
 lean_dec_ref(x_276);
 x_306 = lean_box(0);
}
x_307 = lean_ctor_get(x_277, 0);
lean_inc(x_307);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_308 = x_277;
} else {
 lean_dec_ref(x_277);
 x_308 = lean_box(0);
}
x_309 = l_Lean_mkHole(x_234);
if (lean_is_scalar(x_275)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_275;
 lean_ctor_set_tag(x_310, 0);
}
lean_ctor_set(x_310, 0, x_309);
lean_inc(x_307);
x_311 = l_Lean_mkApp(x_35, x_307);
x_312 = lean_expr_instantiate1(x_273, x_307);
lean_dec(x_273);
if (lean_is_scalar(x_308)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_308;
}
lean_ctor_set(x_313, 0, x_307);
x_314 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_314, 0, x_234);
lean_ctor_set(x_314, 1, x_30);
lean_ctor_set(x_314, 2, x_310);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set(x_3, 1, x_233);
lean_ctor_set(x_3, 0, x_314);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_312);
lean_ctor_set(x_2, 0, x_311);
if (lean_is_scalar(x_306)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_306;
}
lean_ctor_set(x_315, 0, x_2);
lean_ctor_set(x_315, 1, x_305);
x_15 = x_315;
goto block_23;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_234);
lean_free_object(x_29);
lean_dec(x_233);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_316 = lean_ctor_get(x_276, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_276, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_318 = x_276;
} else {
 lean_dec_ref(x_276);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
x_15 = x_319;
goto block_23;
}
}
default: 
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_320 = lean_ctor_get(x_238, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_238, 2);
lean_inc(x_321);
lean_dec(x_238);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_320);
x_323 = lean_ctor_get(x_8, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_8, 1);
lean_inc(x_324);
x_325 = lean_ctor_get(x_8, 2);
lean_inc(x_325);
x_326 = lean_ctor_get(x_8, 3);
lean_inc(x_326);
x_327 = l_Lean_replaceRef(x_234, x_326);
x_328 = l_Lean_replaceRef(x_327, x_326);
lean_dec(x_327);
x_329 = l_Lean_replaceRef(x_328, x_326);
lean_dec(x_326);
lean_dec(x_328);
x_330 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_330, 0, x_323);
lean_ctor_set(x_330, 1, x_324);
lean_ctor_set(x_330, 2, x_325);
lean_ctor_set(x_330, 3, x_329);
x_331 = 0;
x_332 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_333 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_322, x_331, x_332, x_4, x_5, x_6, x_7, x_330, x_9, x_239);
lean_dec(x_330);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_336 = x_333;
} else {
 lean_dec_ref(x_333);
 x_336 = lean_box(0);
}
x_337 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_334);
lean_inc(x_337);
x_338 = l_Lean_mkApp(x_35, x_337);
x_339 = lean_expr_instantiate1(x_321, x_337);
lean_dec(x_321);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_337);
x_341 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_341, 0, x_234);
lean_ctor_set(x_341, 1, x_30);
lean_ctor_set(x_341, 2, x_235);
lean_ctor_set(x_341, 3, x_340);
lean_ctor_set(x_3, 1, x_233);
lean_ctor_set(x_3, 0, x_341);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 0, x_339);
lean_ctor_set(x_2, 0, x_338);
if (lean_is_scalar(x_336)) {
 x_342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_342 = x_336;
}
lean_ctor_set(x_342, 0, x_2);
lean_ctor_set(x_342, 1, x_335);
x_15 = x_342;
goto block_23;
}
}
}
else
{
lean_object* x_343; 
lean_dec(x_235);
lean_free_object(x_29);
lean_dec(x_233);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_343 = lean_box(0);
x_240 = x_343;
goto block_253;
}
block_253:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_240);
x_241 = l_Lean_indentExpr(x_238);
x_242 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_243 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_241);
x_244 = lean_ctor_get(x_8, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_8, 1);
lean_inc(x_245);
x_246 = lean_ctor_get(x_8, 2);
lean_inc(x_246);
x_247 = lean_ctor_get(x_8, 3);
lean_inc(x_247);
x_248 = l_Lean_replaceRef(x_234, x_247);
lean_dec(x_234);
x_249 = l_Lean_replaceRef(x_248, x_247);
lean_dec(x_248);
x_250 = l_Lean_replaceRef(x_249, x_247);
lean_dec(x_247);
lean_dec(x_249);
x_251 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_251, 0, x_244);
lean_ctor_set(x_251, 1, x_245);
lean_ctor_set(x_251, 2, x_246);
lean_ctor_set(x_251, 3, x_250);
lean_inc(x_4);
lean_inc(x_1);
x_252 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_236, x_1, x_243, x_4, x_5, x_6, x_7, x_251, x_9, x_239);
lean_dec(x_251);
x_15 = x_252;
goto block_23;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_free_object(x_29);
lean_dec(x_233);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_344 = lean_ctor_get(x_237, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_237, 1);
lean_inc(x_345);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_346 = x_237;
} else {
 lean_dec_ref(x_237);
 x_346 = lean_box(0);
}
if (lean_is_scalar(x_346)) {
 x_347 = lean_alloc_ctor(1, 2, 0);
} else {
 x_347 = x_346;
}
lean_ctor_set(x_347, 0, x_344);
lean_ctor_set(x_347, 1, x_345);
x_15 = x_347;
goto block_23;
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_348 = lean_ctor_get(x_29, 0);
x_349 = lean_ctor_get(x_29, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_29);
x_350 = lean_ctor_get(x_13, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_13, 2);
lean_inc(x_351);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_352 = x_13;
} else {
 lean_dec_ref(x_13);
 x_352 = lean_box(0);
}
x_353 = lean_ctor_get(x_32, 1);
lean_inc(x_353);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_354 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_348, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
if (lean_obj_tag(x_355) == 7)
{
lean_dec(x_353);
switch (lean_obj_tag(x_351)) {
case 0:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; 
x_371 = lean_ctor_get(x_355, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_355, 2);
lean_inc(x_372);
lean_dec(x_355);
x_373 = lean_ctor_get(x_351, 0);
lean_inc(x_373);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_371);
x_375 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_376 = l_Lean_Elab_Term_elabTermEnsuringType(x_373, x_374, x_375, x_4, x_5, x_6, x_7, x_8, x_9, x_356);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_379 = x_376;
} else {
 lean_dec_ref(x_376);
 x_379 = lean_box(0);
}
lean_inc(x_377);
x_380 = l_Lean_mkApp(x_35, x_377);
x_381 = lean_expr_instantiate1(x_372, x_377);
lean_dec(x_372);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_377);
if (lean_is_scalar(x_352)) {
 x_383 = lean_alloc_ctor(0, 4, 0);
} else {
 x_383 = x_352;
}
lean_ctor_set(x_383, 0, x_350);
lean_ctor_set(x_383, 1, x_30);
lean_ctor_set(x_383, 2, x_351);
lean_ctor_set(x_383, 3, x_382);
lean_ctor_set(x_3, 1, x_349);
lean_ctor_set(x_3, 0, x_383);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_3);
lean_ctor_set(x_2, 1, x_384);
lean_ctor_set(x_2, 0, x_380);
if (lean_is_scalar(x_379)) {
 x_385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_385 = x_379;
}
lean_ctor_set(x_385, 0, x_2);
lean_ctor_set(x_385, 1, x_378);
x_15 = x_385;
goto block_23;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_372);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_386 = lean_ctor_get(x_376, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_376, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_388 = x_376;
} else {
 lean_dec_ref(x_376);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
x_15 = x_389;
goto block_23;
}
}
case 1:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_390 = lean_ctor_get(x_355, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_355, 2);
lean_inc(x_391);
lean_dec(x_355);
x_392 = lean_ctor_get(x_351, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_393 = x_351;
} else {
 lean_dec_ref(x_351);
 x_393 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_390);
x_394 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_392, x_390, x_4, x_5, x_6, x_7, x_8, x_9, x_356);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_free_object(x_2);
x_396 = lean_ctor_get(x_394, 1);
lean_inc(x_396);
lean_dec(x_394);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_390);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_397);
x_398 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_392, x_397, x_4, x_5, x_6, x_7, x_8, x_9, x_396);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_404 = l_Lean_Elab_Term_ensureHasType(x_397, x_401, x_4, x_5, x_6, x_7, x_8, x_9, x_400);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_407 = x_404;
} else {
 lean_dec_ref(x_404);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_408 = lean_alloc_ctor(1, 1, 0);
} else {
 x_408 = x_393;
}
lean_ctor_set(x_408, 0, x_402);
lean_inc(x_405);
x_409 = l_Lean_mkApp(x_35, x_405);
x_410 = lean_expr_instantiate1(x_391, x_405);
lean_dec(x_391);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_405);
if (lean_is_scalar(x_352)) {
 x_412 = lean_alloc_ctor(0, 4, 0);
} else {
 x_412 = x_352;
}
lean_ctor_set(x_412, 0, x_350);
lean_ctor_set(x_412, 1, x_30);
lean_ctor_set(x_412, 2, x_408);
lean_ctor_set(x_412, 3, x_411);
lean_ctor_set(x_3, 1, x_349);
lean_ctor_set(x_3, 0, x_412);
if (lean_is_scalar(x_403)) {
 x_413 = lean_alloc_ctor(0, 2, 0);
} else {
 x_413 = x_403;
}
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_3);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_409);
lean_ctor_set(x_414, 1, x_413);
if (lean_is_scalar(x_407)) {
 x_415 = lean_alloc_ctor(0, 2, 0);
} else {
 x_415 = x_407;
}
lean_ctor_set(x_415, 0, x_414);
lean_ctor_set(x_415, 1, x_406);
x_15 = x_415;
goto block_23;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_416 = lean_ctor_get(x_404, 0);
lean_inc(x_416);
x_417 = lean_ctor_get(x_404, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_418 = x_404;
} else {
 lean_dec_ref(x_404);
 x_418 = lean_box(0);
}
if (lean_is_scalar(x_418)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_418;
}
lean_ctor_set(x_419, 0, x_416);
lean_ctor_set(x_419, 1, x_417);
x_15 = x_419;
goto block_23;
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_397);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_420 = lean_ctor_get(x_398, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_398, 1);
lean_inc(x_421);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_422 = x_398;
} else {
 lean_dec_ref(x_398);
 x_422 = lean_box(0);
}
if (lean_is_scalar(x_422)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_422;
}
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_421);
x_15 = x_423;
goto block_23;
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_392);
lean_dec(x_390);
x_424 = lean_ctor_get(x_394, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_425 = x_394;
} else {
 lean_dec_ref(x_394);
 x_425 = lean_box(0);
}
x_426 = lean_ctor_get(x_395, 0);
lean_inc(x_426);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_427 = x_395;
} else {
 lean_dec_ref(x_395);
 x_427 = lean_box(0);
}
x_428 = l_Lean_mkHole(x_350);
if (lean_is_scalar(x_393)) {
 x_429 = lean_alloc_ctor(0, 1, 0);
} else {
 x_429 = x_393;
 lean_ctor_set_tag(x_429, 0);
}
lean_ctor_set(x_429, 0, x_428);
lean_inc(x_426);
x_430 = l_Lean_mkApp(x_35, x_426);
x_431 = lean_expr_instantiate1(x_391, x_426);
lean_dec(x_391);
if (lean_is_scalar(x_427)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_427;
}
lean_ctor_set(x_432, 0, x_426);
if (lean_is_scalar(x_352)) {
 x_433 = lean_alloc_ctor(0, 4, 0);
} else {
 x_433 = x_352;
}
lean_ctor_set(x_433, 0, x_350);
lean_ctor_set(x_433, 1, x_30);
lean_ctor_set(x_433, 2, x_429);
lean_ctor_set(x_433, 3, x_432);
lean_ctor_set(x_3, 1, x_349);
lean_ctor_set(x_3, 0, x_433);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_431);
lean_ctor_set(x_434, 1, x_3);
lean_ctor_set(x_2, 1, x_434);
lean_ctor_set(x_2, 0, x_430);
if (lean_is_scalar(x_425)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_425;
}
lean_ctor_set(x_435, 0, x_2);
lean_ctor_set(x_435, 1, x_424);
x_15 = x_435;
goto block_23;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_393);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_349);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_436 = lean_ctor_get(x_394, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_394, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 lean_ctor_release(x_394, 1);
 x_438 = x_394;
} else {
 lean_dec_ref(x_394);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
x_15 = x_439;
goto block_23;
}
}
default: 
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_440 = lean_ctor_get(x_355, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_355, 2);
lean_inc(x_441);
lean_dec(x_355);
x_442 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_442, 0, x_440);
x_443 = lean_ctor_get(x_8, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_8, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_8, 2);
lean_inc(x_445);
x_446 = lean_ctor_get(x_8, 3);
lean_inc(x_446);
x_447 = l_Lean_replaceRef(x_350, x_446);
x_448 = l_Lean_replaceRef(x_447, x_446);
lean_dec(x_447);
x_449 = l_Lean_replaceRef(x_448, x_446);
lean_dec(x_446);
lean_dec(x_448);
x_450 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_450, 0, x_443);
lean_ctor_set(x_450, 1, x_444);
lean_ctor_set(x_450, 2, x_445);
lean_ctor_set(x_450, 3, x_449);
x_451 = 0;
x_452 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_453 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_442, x_451, x_452, x_4, x_5, x_6, x_7, x_450, x_9, x_356);
lean_dec(x_450);
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_456 = x_453;
} else {
 lean_dec_ref(x_453);
 x_456 = lean_box(0);
}
x_457 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_454);
lean_inc(x_457);
x_458 = l_Lean_mkApp(x_35, x_457);
x_459 = lean_expr_instantiate1(x_441, x_457);
lean_dec(x_441);
x_460 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_460, 0, x_457);
if (lean_is_scalar(x_352)) {
 x_461 = lean_alloc_ctor(0, 4, 0);
} else {
 x_461 = x_352;
}
lean_ctor_set(x_461, 0, x_350);
lean_ctor_set(x_461, 1, x_30);
lean_ctor_set(x_461, 2, x_351);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set(x_3, 1, x_349);
lean_ctor_set(x_3, 0, x_461);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_3);
lean_ctor_set(x_2, 1, x_462);
lean_ctor_set(x_2, 0, x_458);
if (lean_is_scalar(x_456)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_456;
}
lean_ctor_set(x_463, 0, x_2);
lean_ctor_set(x_463, 1, x_455);
x_15 = x_463;
goto block_23;
}
}
}
else
{
lean_object* x_464; 
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_349);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_464 = lean_box(0);
x_357 = x_464;
goto block_370;
}
block_370:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_357);
x_358 = l_Lean_indentExpr(x_355);
x_359 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_360 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_358);
x_361 = lean_ctor_get(x_8, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_8, 1);
lean_inc(x_362);
x_363 = lean_ctor_get(x_8, 2);
lean_inc(x_363);
x_364 = lean_ctor_get(x_8, 3);
lean_inc(x_364);
x_365 = l_Lean_replaceRef(x_350, x_364);
lean_dec(x_350);
x_366 = l_Lean_replaceRef(x_365, x_364);
lean_dec(x_365);
x_367 = l_Lean_replaceRef(x_366, x_364);
lean_dec(x_364);
lean_dec(x_366);
x_368 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_368, 0, x_361);
lean_ctor_set(x_368, 1, x_362);
lean_ctor_set(x_368, 2, x_363);
lean_ctor_set(x_368, 3, x_367);
lean_inc(x_4);
lean_inc(x_1);
x_369 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_353, x_1, x_360, x_4, x_5, x_6, x_7, x_368, x_9, x_356);
lean_dec(x_368);
x_15 = x_369;
goto block_23;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_30);
lean_free_object(x_3);
x_465 = lean_ctor_get(x_354, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_354, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_467 = x_354;
} else {
 lean_dec_ref(x_354);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
x_15 = x_468;
goto block_23;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_469 = lean_ctor_get(x_2, 0);
lean_inc(x_469);
lean_dec(x_2);
x_470 = lean_ctor_get(x_29, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_29, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_472 = x_29;
} else {
 lean_dec_ref(x_29);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_13, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_13, 2);
lean_inc(x_474);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 x_475 = x_13;
} else {
 lean_dec_ref(x_13);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_32, 1);
lean_inc(x_476);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_477 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_470, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
lean_dec(x_477);
if (lean_obj_tag(x_478) == 7)
{
lean_dec(x_476);
switch (lean_obj_tag(x_474)) {
case 0:
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; 
x_494 = lean_ctor_get(x_478, 1);
lean_inc(x_494);
x_495 = lean_ctor_get(x_478, 2);
lean_inc(x_495);
lean_dec(x_478);
x_496 = lean_ctor_get(x_474, 0);
lean_inc(x_496);
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_494);
x_498 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_499 = l_Lean_Elab_Term_elabTermEnsuringType(x_496, x_497, x_498, x_4, x_5, x_6, x_7, x_8, x_9, x_479);
if (lean_obj_tag(x_499) == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_499, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_502 = x_499;
} else {
 lean_dec_ref(x_499);
 x_502 = lean_box(0);
}
lean_inc(x_500);
x_503 = l_Lean_mkApp(x_469, x_500);
x_504 = lean_expr_instantiate1(x_495, x_500);
lean_dec(x_495);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_500);
if (lean_is_scalar(x_475)) {
 x_506 = lean_alloc_ctor(0, 4, 0);
} else {
 x_506 = x_475;
}
lean_ctor_set(x_506, 0, x_473);
lean_ctor_set(x_506, 1, x_30);
lean_ctor_set(x_506, 2, x_474);
lean_ctor_set(x_506, 3, x_505);
lean_ctor_set(x_3, 1, x_471);
lean_ctor_set(x_3, 0, x_506);
if (lean_is_scalar(x_472)) {
 x_507 = lean_alloc_ctor(0, 2, 0);
} else {
 x_507 = x_472;
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
lean_dec(x_495);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_510 = lean_ctor_get(x_499, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_499, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_512 = x_499;
} else {
 lean_dec_ref(x_499);
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
case 1:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_514 = lean_ctor_get(x_478, 1);
lean_inc(x_514);
x_515 = lean_ctor_get(x_478, 2);
lean_inc(x_515);
lean_dec(x_478);
x_516 = lean_ctor_get(x_474, 0);
lean_inc(x_516);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 x_517 = x_474;
} else {
 lean_dec_ref(x_474);
 x_517 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_514);
x_518 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_516, x_514, x_4, x_5, x_6, x_7, x_8, x_9, x_479);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_514);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_521);
x_522 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_516, x_521, x_4, x_5, x_6, x_7, x_8, x_9, x_520);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_523, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_527 = x_523;
} else {
 lean_dec_ref(x_523);
 x_527 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_528 = l_Lean_Elab_Term_ensureHasType(x_521, x_525, x_4, x_5, x_6, x_7, x_8, x_9, x_524);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
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
if (lean_is_scalar(x_517)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_517;
}
lean_ctor_set(x_532, 0, x_526);
lean_inc(x_529);
x_533 = l_Lean_mkApp(x_469, x_529);
x_534 = lean_expr_instantiate1(x_515, x_529);
lean_dec(x_515);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_529);
if (lean_is_scalar(x_475)) {
 x_536 = lean_alloc_ctor(0, 4, 0);
} else {
 x_536 = x_475;
}
lean_ctor_set(x_536, 0, x_473);
lean_ctor_set(x_536, 1, x_30);
lean_ctor_set(x_536, 2, x_532);
lean_ctor_set(x_536, 3, x_535);
lean_ctor_set(x_3, 1, x_471);
lean_ctor_set(x_3, 0, x_536);
if (lean_is_scalar(x_527)) {
 x_537 = lean_alloc_ctor(0, 2, 0);
} else {
 x_537 = x_527;
}
lean_ctor_set(x_537, 0, x_534);
lean_ctor_set(x_537, 1, x_3);
if (lean_is_scalar(x_472)) {
 x_538 = lean_alloc_ctor(0, 2, 0);
} else {
 x_538 = x_472;
}
lean_ctor_set(x_538, 0, x_533);
lean_ctor_set(x_538, 1, x_537);
if (lean_is_scalar(x_531)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_531;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_530);
x_15 = x_539;
goto block_23;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_517);
lean_dec(x_515);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_540 = lean_ctor_get(x_528, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_528, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 lean_ctor_release(x_528, 1);
 x_542 = x_528;
} else {
 lean_dec_ref(x_528);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
x_15 = x_543;
goto block_23;
}
}
else
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_521);
lean_dec(x_517);
lean_dec(x_515);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_544 = lean_ctor_get(x_522, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_522, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_522)) {
 lean_ctor_release(x_522, 0);
 lean_ctor_release(x_522, 1);
 x_546 = x_522;
} else {
 lean_dec_ref(x_522);
 x_546 = lean_box(0);
}
if (lean_is_scalar(x_546)) {
 x_547 = lean_alloc_ctor(1, 2, 0);
} else {
 x_547 = x_546;
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_545);
x_15 = x_547;
goto block_23;
}
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_dec(x_516);
lean_dec(x_514);
x_548 = lean_ctor_get(x_518, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_549 = x_518;
} else {
 lean_dec_ref(x_518);
 x_549 = lean_box(0);
}
x_550 = lean_ctor_get(x_519, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_551 = x_519;
} else {
 lean_dec_ref(x_519);
 x_551 = lean_box(0);
}
x_552 = l_Lean_mkHole(x_473);
if (lean_is_scalar(x_517)) {
 x_553 = lean_alloc_ctor(0, 1, 0);
} else {
 x_553 = x_517;
 lean_ctor_set_tag(x_553, 0);
}
lean_ctor_set(x_553, 0, x_552);
lean_inc(x_550);
x_554 = l_Lean_mkApp(x_469, x_550);
x_555 = lean_expr_instantiate1(x_515, x_550);
lean_dec(x_515);
if (lean_is_scalar(x_551)) {
 x_556 = lean_alloc_ctor(1, 1, 0);
} else {
 x_556 = x_551;
}
lean_ctor_set(x_556, 0, x_550);
if (lean_is_scalar(x_475)) {
 x_557 = lean_alloc_ctor(0, 4, 0);
} else {
 x_557 = x_475;
}
lean_ctor_set(x_557, 0, x_473);
lean_ctor_set(x_557, 1, x_30);
lean_ctor_set(x_557, 2, x_553);
lean_ctor_set(x_557, 3, x_556);
lean_ctor_set(x_3, 1, x_471);
lean_ctor_set(x_3, 0, x_557);
if (lean_is_scalar(x_472)) {
 x_558 = lean_alloc_ctor(0, 2, 0);
} else {
 x_558 = x_472;
}
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_3);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_554);
lean_ctor_set(x_559, 1, x_558);
if (lean_is_scalar(x_549)) {
 x_560 = lean_alloc_ctor(0, 2, 0);
} else {
 x_560 = x_549;
}
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_548);
x_15 = x_560;
goto block_23;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_475);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_561 = lean_ctor_get(x_518, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_518, 1);
lean_inc(x_562);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_563 = x_518;
} else {
 lean_dec_ref(x_518);
 x_563 = lean_box(0);
}
if (lean_is_scalar(x_563)) {
 x_564 = lean_alloc_ctor(1, 2, 0);
} else {
 x_564 = x_563;
}
lean_ctor_set(x_564, 0, x_561);
lean_ctor_set(x_564, 1, x_562);
x_15 = x_564;
goto block_23;
}
}
default: 
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_565 = lean_ctor_get(x_478, 1);
lean_inc(x_565);
x_566 = lean_ctor_get(x_478, 2);
lean_inc(x_566);
lean_dec(x_478);
x_567 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_567, 0, x_565);
x_568 = lean_ctor_get(x_8, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_8, 1);
lean_inc(x_569);
x_570 = lean_ctor_get(x_8, 2);
lean_inc(x_570);
x_571 = lean_ctor_get(x_8, 3);
lean_inc(x_571);
x_572 = l_Lean_replaceRef(x_473, x_571);
x_573 = l_Lean_replaceRef(x_572, x_571);
lean_dec(x_572);
x_574 = l_Lean_replaceRef(x_573, x_571);
lean_dec(x_571);
lean_dec(x_573);
x_575 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_575, 0, x_568);
lean_ctor_set(x_575, 1, x_569);
lean_ctor_set(x_575, 2, x_570);
lean_ctor_set(x_575, 3, x_574);
x_576 = 0;
x_577 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_578 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_567, x_576, x_577, x_4, x_5, x_6, x_7, x_575, x_9, x_479);
lean_dec(x_575);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_578, 1);
lean_inc(x_580);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 lean_ctor_release(x_578, 1);
 x_581 = x_578;
} else {
 lean_dec_ref(x_578);
 x_581 = lean_box(0);
}
x_582 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_579);
lean_inc(x_582);
x_583 = l_Lean_mkApp(x_469, x_582);
x_584 = lean_expr_instantiate1(x_566, x_582);
lean_dec(x_566);
x_585 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_585, 0, x_582);
if (lean_is_scalar(x_475)) {
 x_586 = lean_alloc_ctor(0, 4, 0);
} else {
 x_586 = x_475;
}
lean_ctor_set(x_586, 0, x_473);
lean_ctor_set(x_586, 1, x_30);
lean_ctor_set(x_586, 2, x_474);
lean_ctor_set(x_586, 3, x_585);
lean_ctor_set(x_3, 1, x_471);
lean_ctor_set(x_3, 0, x_586);
if (lean_is_scalar(x_472)) {
 x_587 = lean_alloc_ctor(0, 2, 0);
} else {
 x_587 = x_472;
}
lean_ctor_set(x_587, 0, x_584);
lean_ctor_set(x_587, 1, x_3);
x_588 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_588, 0, x_583);
lean_ctor_set(x_588, 1, x_587);
if (lean_is_scalar(x_581)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_581;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_580);
x_15 = x_589;
goto block_23;
}
}
}
else
{
lean_object* x_590; 
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_590 = lean_box(0);
x_480 = x_590;
goto block_493;
}
block_493:
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_480);
x_481 = l_Lean_indentExpr(x_478);
x_482 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_483 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_481);
x_484 = lean_ctor_get(x_8, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_8, 1);
lean_inc(x_485);
x_486 = lean_ctor_get(x_8, 2);
lean_inc(x_486);
x_487 = lean_ctor_get(x_8, 3);
lean_inc(x_487);
x_488 = l_Lean_replaceRef(x_473, x_487);
lean_dec(x_473);
x_489 = l_Lean_replaceRef(x_488, x_487);
lean_dec(x_488);
x_490 = l_Lean_replaceRef(x_489, x_487);
lean_dec(x_487);
lean_dec(x_489);
x_491 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_491, 0, x_484);
lean_ctor_set(x_491, 1, x_485);
lean_ctor_set(x_491, 2, x_486);
lean_ctor_set(x_491, 3, x_490);
lean_inc(x_4);
lean_inc(x_1);
x_492 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_476, x_1, x_483, x_4, x_5, x_6, x_7, x_491, x_9, x_479);
lean_dec(x_491);
x_15 = x_492;
goto block_23;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_476);
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_472);
lean_dec(x_471);
lean_dec(x_469);
lean_dec(x_30);
lean_free_object(x_3);
x_591 = lean_ctor_get(x_477, 0);
lean_inc(x_591);
x_592 = lean_ctor_get(x_477, 1);
lean_inc(x_592);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_593 = x_477;
} else {
 lean_dec_ref(x_477);
 x_593 = lean_box(0);
}
if (lean_is_scalar(x_593)) {
 x_594 = lean_alloc_ctor(1, 2, 0);
} else {
 x_594 = x_593;
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_592);
x_15 = x_594;
goto block_23;
}
}
}
else
{
lean_object* x_595; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_595 = lean_box(0);
x_24 = x_595;
goto block_28;
}
}
else
{
lean_object* x_596; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_free_object(x_3);
lean_dec(x_2);
x_596 = lean_box(0);
x_24 = x_596;
goto block_28;
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
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_4);
x_27 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_25, x_26, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_25);
x_15 = x_27;
goto block_23;
}
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_608; lean_object* x_613; lean_object* x_614; 
x_597 = lean_ctor_get(x_3, 0);
x_598 = lean_ctor_get(x_3, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_3);
x_613 = lean_ctor_get(x_2, 1);
lean_inc(x_613);
x_614 = lean_ctor_get(x_597, 1);
lean_inc(x_614);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; 
lean_dec(x_613);
lean_dec(x_2);
x_615 = lean_box(0);
x_608 = x_615;
goto block_612;
}
else
{
lean_object* x_616; 
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_614, 1);
lean_inc(x_617);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_618 = lean_ctor_get(x_2, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_619 = x_2;
} else {
 lean_dec_ref(x_2);
 x_619 = lean_box(0);
}
x_620 = lean_ctor_get(x_613, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_613, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_622 = x_613;
} else {
 lean_dec_ref(x_613);
 x_622 = lean_box(0);
}
x_623 = lean_ctor_get(x_597, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_597, 2);
lean_inc(x_624);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 lean_ctor_release(x_597, 1);
 lean_ctor_release(x_597, 2);
 lean_ctor_release(x_597, 3);
 x_625 = x_597;
} else {
 lean_dec_ref(x_597);
 x_625 = lean_box(0);
}
x_626 = lean_ctor_get(x_616, 1);
lean_inc(x_626);
lean_dec(x_616);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_627 = l_Lean_Meta_whnfForall___at___private_Lean_Elab_Term_18__useImplicitLambda_x3f___spec__1(x_620, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_627) == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_627, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_627, 1);
lean_inc(x_629);
lean_dec(x_627);
if (lean_obj_tag(x_628) == 7)
{
lean_dec(x_626);
switch (lean_obj_tag(x_624)) {
case 0:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; lean_object* x_649; 
x_644 = lean_ctor_get(x_628, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_628, 2);
lean_inc(x_645);
lean_dec(x_628);
x_646 = lean_ctor_get(x_624, 0);
lean_inc(x_646);
x_647 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_647, 0, x_644);
x_648 = 1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_649 = l_Lean_Elab_Term_elabTermEnsuringType(x_646, x_647, x_648, x_4, x_5, x_6, x_7, x_8, x_9, x_629);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_649, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_652 = x_649;
} else {
 lean_dec_ref(x_649);
 x_652 = lean_box(0);
}
lean_inc(x_650);
x_653 = l_Lean_mkApp(x_618, x_650);
x_654 = lean_expr_instantiate1(x_645, x_650);
lean_dec(x_645);
x_655 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_655, 0, x_650);
if (lean_is_scalar(x_625)) {
 x_656 = lean_alloc_ctor(0, 4, 0);
} else {
 x_656 = x_625;
}
lean_ctor_set(x_656, 0, x_623);
lean_ctor_set(x_656, 1, x_614);
lean_ctor_set(x_656, 2, x_624);
lean_ctor_set(x_656, 3, x_655);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_621);
if (lean_is_scalar(x_622)) {
 x_658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_658 = x_622;
}
lean_ctor_set(x_658, 0, x_654);
lean_ctor_set(x_658, 1, x_657);
if (lean_is_scalar(x_619)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_619;
}
lean_ctor_set(x_659, 0, x_653);
lean_ctor_set(x_659, 1, x_658);
if (lean_is_scalar(x_652)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_652;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_651);
x_599 = x_660;
goto block_607;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_645);
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_614);
x_661 = lean_ctor_get(x_649, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_649, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_649)) {
 lean_ctor_release(x_649, 0);
 lean_ctor_release(x_649, 1);
 x_663 = x_649;
} else {
 lean_dec_ref(x_649);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 2, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_661);
lean_ctor_set(x_664, 1, x_662);
x_599 = x_664;
goto block_607;
}
}
case 1:
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_665 = lean_ctor_get(x_628, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_628, 2);
lean_inc(x_666);
lean_dec(x_628);
x_667 = lean_ctor_get(x_624, 0);
lean_inc(x_667);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 x_668 = x_624;
} else {
 lean_dec_ref(x_624);
 x_668 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_665);
x_669 = l_Lean_Elab_Term_StructInst_trySynthStructInstance_x3f(x_667, x_665, x_4, x_5, x_6, x_7, x_8, x_9, x_629);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_619);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_672 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_672, 0, x_665);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_672);
x_673 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_667, x_672, x_4, x_5, x_6, x_7, x_8, x_9, x_671);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_ctor_get(x_674, 0);
lean_inc(x_676);
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_678 = x_674;
} else {
 lean_dec_ref(x_674);
 x_678 = lean_box(0);
}
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_679 = l_Lean_Elab_Term_ensureHasType(x_672, x_676, x_4, x_5, x_6, x_7, x_8, x_9, x_675);
if (lean_obj_tag(x_679) == 0)
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_680 = lean_ctor_get(x_679, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_679, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_682 = x_679;
} else {
 lean_dec_ref(x_679);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_668)) {
 x_683 = lean_alloc_ctor(1, 1, 0);
} else {
 x_683 = x_668;
}
lean_ctor_set(x_683, 0, x_677);
lean_inc(x_680);
x_684 = l_Lean_mkApp(x_618, x_680);
x_685 = lean_expr_instantiate1(x_666, x_680);
lean_dec(x_666);
x_686 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_686, 0, x_680);
if (lean_is_scalar(x_625)) {
 x_687 = lean_alloc_ctor(0, 4, 0);
} else {
 x_687 = x_625;
}
lean_ctor_set(x_687, 0, x_623);
lean_ctor_set(x_687, 1, x_614);
lean_ctor_set(x_687, 2, x_683);
lean_ctor_set(x_687, 3, x_686);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_621);
if (lean_is_scalar(x_678)) {
 x_689 = lean_alloc_ctor(0, 2, 0);
} else {
 x_689 = x_678;
}
lean_ctor_set(x_689, 0, x_685);
lean_ctor_set(x_689, 1, x_688);
if (lean_is_scalar(x_622)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_622;
}
lean_ctor_set(x_690, 0, x_684);
lean_ctor_set(x_690, 1, x_689);
if (lean_is_scalar(x_682)) {
 x_691 = lean_alloc_ctor(0, 2, 0);
} else {
 x_691 = x_682;
}
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_681);
x_599 = x_691;
goto block_607;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_678);
lean_dec(x_677);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_618);
lean_dec(x_614);
x_692 = lean_ctor_get(x_679, 0);
lean_inc(x_692);
x_693 = lean_ctor_get(x_679, 1);
lean_inc(x_693);
if (lean_is_exclusive(x_679)) {
 lean_ctor_release(x_679, 0);
 lean_ctor_release(x_679, 1);
 x_694 = x_679;
} else {
 lean_dec_ref(x_679);
 x_694 = lean_box(0);
}
if (lean_is_scalar(x_694)) {
 x_695 = lean_alloc_ctor(1, 2, 0);
} else {
 x_695 = x_694;
}
lean_ctor_set(x_695, 0, x_692);
lean_ctor_set(x_695, 1, x_693);
x_599 = x_695;
goto block_607;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_672);
lean_dec(x_668);
lean_dec(x_666);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_618);
lean_dec(x_614);
x_696 = lean_ctor_get(x_673, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_673, 1);
lean_inc(x_697);
if (lean_is_exclusive(x_673)) {
 lean_ctor_release(x_673, 0);
 lean_ctor_release(x_673, 1);
 x_698 = x_673;
} else {
 lean_dec_ref(x_673);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 2, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_696);
lean_ctor_set(x_699, 1, x_697);
x_599 = x_699;
goto block_607;
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_667);
lean_dec(x_665);
x_700 = lean_ctor_get(x_669, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_701 = x_669;
} else {
 lean_dec_ref(x_669);
 x_701 = lean_box(0);
}
x_702 = lean_ctor_get(x_670, 0);
lean_inc(x_702);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 x_703 = x_670;
} else {
 lean_dec_ref(x_670);
 x_703 = lean_box(0);
}
x_704 = l_Lean_mkHole(x_623);
if (lean_is_scalar(x_668)) {
 x_705 = lean_alloc_ctor(0, 1, 0);
} else {
 x_705 = x_668;
 lean_ctor_set_tag(x_705, 0);
}
lean_ctor_set(x_705, 0, x_704);
lean_inc(x_702);
x_706 = l_Lean_mkApp(x_618, x_702);
x_707 = lean_expr_instantiate1(x_666, x_702);
lean_dec(x_666);
if (lean_is_scalar(x_703)) {
 x_708 = lean_alloc_ctor(1, 1, 0);
} else {
 x_708 = x_703;
}
lean_ctor_set(x_708, 0, x_702);
if (lean_is_scalar(x_625)) {
 x_709 = lean_alloc_ctor(0, 4, 0);
} else {
 x_709 = x_625;
}
lean_ctor_set(x_709, 0, x_623);
lean_ctor_set(x_709, 1, x_614);
lean_ctor_set(x_709, 2, x_705);
lean_ctor_set(x_709, 3, x_708);
x_710 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_621);
if (lean_is_scalar(x_622)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_622;
}
lean_ctor_set(x_711, 0, x_707);
lean_ctor_set(x_711, 1, x_710);
if (lean_is_scalar(x_619)) {
 x_712 = lean_alloc_ctor(0, 2, 0);
} else {
 x_712 = x_619;
}
lean_ctor_set(x_712, 0, x_706);
lean_ctor_set(x_712, 1, x_711);
if (lean_is_scalar(x_701)) {
 x_713 = lean_alloc_ctor(0, 2, 0);
} else {
 x_713 = x_701;
}
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_700);
x_599 = x_713;
goto block_607;
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_625);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_614);
x_714 = lean_ctor_get(x_669, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_669, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_716 = x_669;
} else {
 lean_dec_ref(x_669);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_714);
lean_ctor_set(x_717, 1, x_715);
x_599 = x_717;
goto block_607;
}
}
default: 
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; uint8_t x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
x_718 = lean_ctor_get(x_628, 1);
lean_inc(x_718);
x_719 = lean_ctor_get(x_628, 2);
lean_inc(x_719);
lean_dec(x_628);
x_720 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_720, 0, x_718);
x_721 = lean_ctor_get(x_8, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_8, 1);
lean_inc(x_722);
x_723 = lean_ctor_get(x_8, 2);
lean_inc(x_723);
x_724 = lean_ctor_get(x_8, 3);
lean_inc(x_724);
x_725 = l_Lean_replaceRef(x_623, x_724);
x_726 = l_Lean_replaceRef(x_725, x_724);
lean_dec(x_725);
x_727 = l_Lean_replaceRef(x_726, x_724);
lean_dec(x_724);
lean_dec(x_726);
x_728 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_728, 0, x_721);
lean_ctor_set(x_728, 1, x_722);
lean_ctor_set(x_728, 2, x_723);
lean_ctor_set(x_728, 3, x_727);
x_729 = 0;
x_730 = lean_box(0);
lean_inc(x_6);
lean_inc(x_4);
x_731 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_720, x_729, x_730, x_4, x_5, x_6, x_7, x_728, x_9, x_629);
lean_dec(x_728);
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_734 = x_731;
} else {
 lean_dec_ref(x_731);
 x_734 = lean_box(0);
}
x_735 = l_Lean_Elab_Term_StructInst_markDefaultMissing(x_732);
lean_inc(x_735);
x_736 = l_Lean_mkApp(x_618, x_735);
x_737 = lean_expr_instantiate1(x_719, x_735);
lean_dec(x_719);
x_738 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_738, 0, x_735);
if (lean_is_scalar(x_625)) {
 x_739 = lean_alloc_ctor(0, 4, 0);
} else {
 x_739 = x_625;
}
lean_ctor_set(x_739, 0, x_623);
lean_ctor_set(x_739, 1, x_614);
lean_ctor_set(x_739, 2, x_624);
lean_ctor_set(x_739, 3, x_738);
x_740 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_621);
if (lean_is_scalar(x_622)) {
 x_741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_741 = x_622;
}
lean_ctor_set(x_741, 0, x_737);
lean_ctor_set(x_741, 1, x_740);
if (lean_is_scalar(x_619)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_619;
}
lean_ctor_set(x_742, 0, x_736);
lean_ctor_set(x_742, 1, x_741);
if (lean_is_scalar(x_734)) {
 x_743 = lean_alloc_ctor(0, 2, 0);
} else {
 x_743 = x_734;
}
lean_ctor_set(x_743, 0, x_742);
lean_ctor_set(x_743, 1, x_733);
x_599 = x_743;
goto block_607;
}
}
}
else
{
lean_object* x_744; 
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_614);
x_744 = lean_box(0);
x_630 = x_744;
goto block_643;
}
block_643:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_630);
x_631 = l_Lean_indentExpr(x_628);
x_632 = l___private_Lean_Elab_StructInst_20__mkCtorHeaderAux___main___closed__3;
x_633 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
x_634 = lean_ctor_get(x_8, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_8, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_8, 2);
lean_inc(x_636);
x_637 = lean_ctor_get(x_8, 3);
lean_inc(x_637);
x_638 = l_Lean_replaceRef(x_623, x_637);
lean_dec(x_623);
x_639 = l_Lean_replaceRef(x_638, x_637);
lean_dec(x_638);
x_640 = l_Lean_replaceRef(x_639, x_637);
lean_dec(x_637);
lean_dec(x_639);
x_641 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_641, 0, x_634);
lean_ctor_set(x_641, 1, x_635);
lean_ctor_set(x_641, 2, x_636);
lean_ctor_set(x_641, 3, x_640);
lean_inc(x_4);
lean_inc(x_1);
x_642 = l_Lean_Elab_Term_StructInst_throwFailedToElabField___rarg(x_626, x_1, x_633, x_4, x_5, x_6, x_7, x_641, x_9, x_629);
lean_dec(x_641);
x_599 = x_642;
goto block_607;
}
}
else
{
lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_626);
lean_dec(x_625);
lean_dec(x_624);
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_614);
x_745 = lean_ctor_get(x_627, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_627, 1);
lean_inc(x_746);
if (lean_is_exclusive(x_627)) {
 lean_ctor_release(x_627, 0);
 lean_ctor_release(x_627, 1);
 x_747 = x_627;
} else {
 lean_dec_ref(x_627);
 x_747 = lean_box(0);
}
if (lean_is_scalar(x_747)) {
 x_748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_748 = x_747;
}
lean_ctor_set(x_748, 0, x_745);
lean_ctor_set(x_748, 1, x_746);
x_599 = x_748;
goto block_607;
}
}
else
{
lean_object* x_749; 
lean_dec(x_617);
lean_dec(x_616);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_2);
x_749 = lean_box(0);
x_608 = x_749;
goto block_612;
}
}
else
{
lean_object* x_750; 
lean_dec(x_616);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_2);
x_750 = lean_box(0);
x_608 = x_750;
goto block_612;
}
}
block_607:
{
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
x_2 = x_600;
x_3 = x_598;
x_10 = x_601;
goto _start;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
lean_dec(x_598);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_603 = lean_ctor_get(x_599, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_599, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_605 = x_599;
} else {
 lean_dec_ref(x_599);
 x_605 = lean_box(0);
}
if (lean_is_scalar(x_605)) {
 x_606 = lean_alloc_ctor(1, 2, 0);
} else {
 x_606 = x_605;
}
lean_ctor_set(x_606, 0, x_603);
lean_ctor_set(x_606, 1, x_604);
return x_606;
}
}
block_612:
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_608);
x_609 = lean_ctor_get(x_597, 0);
lean_inc(x_609);
lean_dec(x_597);
x_610 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1___closed__3;
lean_inc(x_4);
x_611 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_21__elabTermAux___main___spec__1___rarg(x_609, x_610, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_609);
x_599 = x_611;
goto block_607;
}
}
}
}
}
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_7, 3);
x_13 = l_Lean_replaceRef(x_10, x_12);
lean_dec(x_10);
x_14 = l_Lean_replaceRef(x_13, x_12);
lean_dec(x_13);
x_15 = l_Lean_replaceRef(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
lean_ctor_set(x_7, 3, x_15);
x_16 = lean_st_ref_get(x_8, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_20);
x_21 = l_Lean_getStructureCtor(x_19, x_20);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_31 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_20, x_29, x_30, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_32, 0);
lean_inc(x_36);
lean_dec(x_32);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
x_39 = lean_ctor_get(x_33, 0);
lean_dec(x_39);
x_40 = l_List_reverse___rarg(x_38);
x_41 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_40);
lean_ctor_set(x_33, 1, x_41);
lean_ctor_set(x_33, 0, x_36);
lean_ctor_set(x_31, 0, x_33);
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = l_List_reverse___rarg(x_42);
x_44 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_31, 0, x_45);
return x_31;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_dec(x_31);
x_47 = lean_ctor_get(x_32, 0);
lean_inc(x_47);
lean_dec(x_32);
x_48 = lean_ctor_get(x_33, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_49 = x_33;
} else {
 lean_dec_ref(x_33);
 x_49 = lean_box(0);
}
x_50 = l_List_reverse___rarg(x_48);
x_51 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_50);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_46);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
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
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
x_64 = lean_ctor_get(x_7, 2);
x_65 = lean_ctor_get(x_7, 3);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_66 = l_Lean_replaceRef(x_10, x_65);
lean_dec(x_10);
x_67 = l_Lean_replaceRef(x_66, x_65);
lean_dec(x_66);
x_68 = l_Lean_replaceRef(x_67, x_65);
lean_dec(x_65);
lean_dec(x_67);
x_69 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_68);
x_70 = lean_st_ref_get(x_8, x_9);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_Elab_Term_StructInst_Struct_structName(x_1);
lean_inc(x_74);
x_75 = l_Lean_getStructureCtor(x_73, x_74);
lean_inc(x_8);
lean_inc(x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_76 = l___private_Lean_Elab_StructInst_23__mkCtorHeader(x_75, x_2, x_3, x_4, x_5, x_6, x_69, x_8, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_StructInst_Struct_fields(x_1);
x_85 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_24__elabStruct___main___spec__1(x_74, x_83, x_84, x_3, x_4, x_5, x_6, x_69, x_8, x_78);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_92 = x_87;
} else {
 lean_dec_ref(x_87);
 x_92 = lean_box(0);
}
x_93 = l_List_reverse___rarg(x_91);
x_94 = l_Lean_Elab_Term_StructInst_Struct_setFields(x_1, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_89;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_88);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_85, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_85, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_99 = x_85;
} else {
 lean_dec_ref(x_85);
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
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = lean_ctor_get(x_76, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_76, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_103 = x_76;
} else {
 lean_dec_ref(x_76);
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
}
}
lean_object* l___private_Lean_Elab_StructInst_24__elabStruct(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_isRoundDone(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = 0;
x_16 = lean_box(x_15);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_10, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
x_26 = lean_box(x_25);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_lt(x_29, x_28);
x_31 = lean_box(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_24 = l_Lean_Elab_Term_StructInst_Struct_ref(x_1);
x_25 = (uint8_t)((x_23 << 24) >> 61);
x_26 = l_Lean_BinderInfo_isExplicit(x_25);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_7, 3);
x_29 = l_Lean_replaceRef(x_24, x_28);
lean_dec(x_24);
x_30 = l_Lean_replaceRef(x_29, x_28);
lean_dec(x_29);
x_31 = l_Lean_replaceRef(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
lean_ctor_set(x_7, 3, x_31);
if (x_26 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_20);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_21);
x_33 = 0;
x_34 = lean_box(0);
lean_inc(x_5);
lean_inc(x_3);
x_35 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_32, x_33, x_34, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_expr_instantiate1(x_22, x_36);
lean_dec(x_36);
lean_dec(x_22);
x_2 = x_38;
x_9 = x_37;
goto _start;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_20);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_9);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_42);
x_43 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_42, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_46 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_44, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_dec(x_46);
x_56 = lean_expr_instantiate1(x_22, x_42);
lean_dec(x_42);
lean_dec(x_22);
x_2 = x_56;
x_9 = x_55;
goto _start;
}
}
else
{
uint8_t x_58; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_42);
lean_dec(x_7);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_43);
if (x_62 == 0)
{
return x_43;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_43, 0);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_7, 0);
x_67 = lean_ctor_get(x_7, 1);
x_68 = lean_ctor_get(x_7, 2);
x_69 = lean_ctor_get(x_7, 3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_7);
x_70 = l_Lean_replaceRef(x_24, x_69);
lean_dec(x_24);
x_71 = l_Lean_replaceRef(x_70, x_69);
lean_dec(x_70);
x_72 = l_Lean_replaceRef(x_71, x_69);
lean_dec(x_69);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_66);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_72);
if (x_26 == 0)
{
lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_20);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_21);
x_75 = 0;
x_76 = lean_box(0);
lean_inc(x_5);
lean_inc(x_3);
x_77 = l_Lean_Meta_mkFreshExprMVar___at_Lean_Elab_Term_tryCoe___spec__2(x_74, x_75, x_76, x_3, x_4, x_5, x_6, x_73, x_8, x_9);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_expr_instantiate1(x_22, x_78);
lean_dec(x_78);
lean_dec(x_22);
x_2 = x_80;
x_7 = x_73;
x_9 = x_79;
goto _start;
}
else
{
lean_object* x_82; 
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldValue_x3f(x_1, x_20);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_9);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_84);
x_85 = l_Lean_Meta_inferType___at_Lean_Elab_Term_tryLiftAndCoe___spec__2(x_84, x_3, x_4, x_5, x_6, x_73, x_8, x_9);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_8);
lean_inc(x_73);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_88 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_isDefEqNoConstantApprox___spec__1(x_86, x_21, x_3, x_4, x_5, x_6, x_73, x_8, x_87);
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
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
x_96 = lean_expr_instantiate1(x_22, x_84);
lean_dec(x_84);
lean_dec(x_22);
x_2 = x_96;
x_7 = x_73;
x_9 = x_95;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_84);
lean_dec(x_73);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_106 = lean_box(0);
x_10 = x_106;
goto block_19;
}
block_19:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = l___private_Lean_Meta_AppBuilder_1__mkIdImp___closed__2;
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_2, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
return x_18;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_7, 3);
x_14 = l_Lean_replaceRef(x_10, x_13);
lean_dec(x_10);
x_15 = l_Lean_replaceRef(x_14, x_13);
lean_dec(x_14);
x_16 = l_Lean_replaceRef(x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_ctor_set(x_7, 3, x_16);
lean_inc(x_3);
x_17 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_instantiate_value_lparams(x_2, x_18);
lean_dec(x_18);
x_21 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_20, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
x_24 = lean_ctor_get(x_7, 2);
x_25 = lean_ctor_get(x_7, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_26 = l_Lean_replaceRef(x_10, x_25);
lean_dec(x_10);
x_27 = l_Lean_replaceRef(x_26, x_25);
lean_dec(x_26);
x_28 = l_Lean_replaceRef(x_27, x_25);
lean_dec(x_25);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_24);
lean_ctor_set(x_29, 3, x_28);
lean_inc(x_3);
x_30 = l_List_mapM___main___at___private_Lean_Elab_StructInst_23__mkCtorHeader___spec__1(x_11, x_3, x_4, x_5, x_6, x_29, x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_instantiate_value_lparams(x_2, x_31);
lean_dec(x_31);
x_34 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValueAux_x3f___main(x_1, x_33, x_3, x_4, x_5, x_6, x_29, x_8, x_32);
return x_34;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
x_11 = l_Lean_Expr_getAppFn___main(x_2);
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
x_21 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_20);
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
x_23 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_2, x_3, x_4, x_5, x_6, x_16);
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
x_31 = l_Array_contains___at_Lean_findField_x3f___main___spec__1(x_1, x_30);
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
x_34 = l___private_Lean_Meta_WHNF_19__unfoldDefinitionImp_x3f(x_2, x_3, x_4, x_5, x_6, x_25);
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
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_3;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_fset(x_3, x_2, x_14);
x_16 = x_13;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = x_18;
x_23 = lean_array_fset(x_15, x_2, x_22);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_23;
x_8 = x_19;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_mkForallFVars___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__1(x_2, x_10, x_4, x_5, x_6, x_7, x_11);
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_getExprMVarAssignment_x3f___at___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___spec__1(x_8, x_3, x_4, x_5, x_6, x_7);
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
x_30 = l_Lean_Expr_getAppFn___main(x_26);
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_31 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_30, x_3, x_4, x_5, x_6, x_29);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_35);
x_37 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_36);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_sub(x_36, x_39);
lean_dec(x_36);
x_41 = l___private_Lean_Expr_3__getAppArgsAux___main(x_2, x_38, x_40);
x_42 = x_41;
x_43 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___spec__1), 8, 3);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_35);
lean_closure_set(x_43, 2, x_42);
x_44 = x_43;
x_45 = lean_apply_5(x_44, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_47, x_47, x_35, x_32);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_49, x_49, x_35, x_32);
lean_dec(x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_32);
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Lean_Expr_getAppNumArgsAux___main(x_2, x_57);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec(x_58);
x_60 = l___private_Lean_Expr_4__getAppRevArgsAux___main(x_2, x_59);
x_61 = l_Lean_Expr_betaRev(x_32, x_60);
lean_dec(x_60);
lean_dec(x_32);
x_2 = x_61;
x_7 = x_33;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_31);
if (x_63 == 0)
{
return x_31;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_31, 0);
x_65 = lean_ctor_get(x_31, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_31);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_26);
lean_dec(x_2);
x_67 = lean_ctor_get(x_27, 1);
lean_inc(x_67);
lean_dec(x_27);
x_68 = lean_ctor_get(x_28, 0);
lean_inc(x_68);
lean_dec(x_28);
x_2 = x_68;
x_7 = x_67;
goto _start;
}
}
else
{
uint8_t x_70; 
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_27);
if (x_70 == 0)
{
return x_27;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_27, 0);
x_72 = lean_ctor_get(x_27, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_27);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 8, 1);
lean_closure_set(x_74, 0, x_1);
x_75 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_2, x_74, x_3, x_4, x_5, x_6, x_7);
return x_75;
}
case 7:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__2), 8, 1);
lean_closure_set(x_76, 0, x_1);
x_77 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_5__inferForallType___spec__3___rarg(x_2, x_76, x_3, x_4, x_5, x_6, x_7);
return x_77;
}
case 8:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_alloc_closure((void*)(l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main___lambda__1), 8, 1);
lean_closure_set(x_78, 0, x_1);
x_79 = l_Lean_Meta_lambdaLetTelescope___at___private_Lean_Meta_InferType_6__inferLambdaType___spec__2___rarg(x_2, x_78, x_3, x_4, x_5, x_6, x_7);
return x_79;
}
case 10:
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_80, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
x_84 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_expr_update_mdata(x_2, x_83);
lean_ctor_set(x_81, 0, x_85);
return x_81;
}
else
{
uint8_t x_86; 
lean_dec(x_84);
x_86 = l_Lean_Expr_isMVar(x_83);
if (x_86 == 0)
{
lean_dec(x_2);
return x_81;
}
else
{
lean_object* x_87; 
x_87 = lean_expr_update_mdata(x_2, x_83);
lean_ctor_set(x_81, 0, x_87);
return x_81;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_81, 0);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_81);
x_90 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_2);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_expr_update_mdata(x_2, x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
uint8_t x_93; 
lean_dec(x_90);
x_93 = l_Lean_Expr_isMVar(x_88);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_2);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_expr_update_mdata(x_2, x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_89);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_81);
if (x_97 == 0)
{
return x_81;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_81, 0);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_81);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
case 11:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_2, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_2, 2);
lean_inc(x_102);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_102);
x_103 = l_Lean_Meta_reduceProj_x3f(x_102, x_101, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_102, x_3, x_4, x_5, x_6, x_105);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_expr_update_proj(x_2, x_108);
lean_ctor_set(x_106, 0, x_109);
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_expr_update_proj(x_2, x_110);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_106, 0);
x_116 = lean_ctor_get(x_106, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_106);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_102);
lean_dec(x_2);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
lean_dec(x_103);
x_119 = lean_ctor_get(x_104, 0);
lean_inc(x_119);
lean_dec(x_104);
x_2 = x_119;
x_7 = x_118;
goto _start;
}
}
else
{
uint8_t x_121; 
lean_dec(x_102);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_103);
if (x_121 == 0)
{
return x_103;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_103, 0);
x_123 = lean_ctor_get(x_103, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_103);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
default: 
{
lean_object* x_125; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_125, 1, x_7);
return x_125;
}
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
x_23 = l_Lean_Name_append___main(x_22, x_4);
lean_dec(x_22);
x_24 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___closed__2;
x_25 = l_Lean_Name_append___main(x_23, x_24);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_st_ref_get(x_11, x_28);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_39 = l_Lean_Elab_Term_StructInst_DefaultFields_mkDefaultValue_x3f(x_21, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_37);
lean_dec(x_34);
lean_dec(x_21);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_8);
x_42 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_6, x_44);
lean_dec(x_6);
x_46 = lean_nat_add(x_7, x_44);
lean_dec(x_7);
x_6 = x_45;
x_7 = x_46;
x_14 = x_43;
goto _start;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_dec(x_39);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_st_ref_get(x_13, x_48);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 2);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_13, x_53);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_56, 2);
lean_dec(x_59);
x_60 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_56, 2, x_60);
x_61 = lean_st_ref_set(x_13, x_56, x_57);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_63 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_50, x_10, x_11, x_12, x_13, x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_8);
x_66 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_65);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = 8192;
x_69 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_64);
x_70 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_68, x_64, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_72 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 2);
lean_inc(x_75);
lean_dec(x_73);
lean_ctor_set(x_40, 0, x_75);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_76 = l_Lean_Elab_Term_ensureHasType(x_40, x_64, x_8, x_9, x_10, x_11, x_12, x_13, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_5, x_77, x_8, x_9, x_10, x_11, x_12, x_13, x_78);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
lean_dec(x_81);
x_82 = 1;
x_83 = lean_box(x_82);
lean_ctor_set(x_79, 0, x_83);
return x_79;
}
else
{
lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_dec(x_79);
x_85 = 1;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_84);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_76);
if (x_88 == 0)
{
return x_76;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_76, 0);
x_90 = lean_ctor_get(x_76, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_76);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_71);
lean_dec(x_64);
lean_free_object(x_40);
lean_inc(x_8);
x_92 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_67);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_6, x_94);
lean_dec(x_6);
x_96 = lean_nat_add(x_7, x_94);
lean_dec(x_7);
x_6 = x_95;
x_7 = x_96;
x_14 = x_93;
goto _start;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_free_object(x_40);
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_63, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_dec(x_63);
x_100 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_99);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
lean_ctor_set_tag(x_100, 1);
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_98);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_56, 0);
x_106 = lean_ctor_get(x_56, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_56);
x_107 = l_Lean_TraceState_Inhabited___closed__1;
x_108 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
lean_ctor_set(x_108, 2, x_107);
x_109 = lean_st_ref_set(x_13, x_108, x_57);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_111 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_50, x_10, x_11, x_12, x_13, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; size_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_8);
x_114 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_113);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = 8192;
x_117 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_112);
x_118 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_116, x_112, x_117);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_120 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_115);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_121, 2);
lean_inc(x_123);
lean_dec(x_121);
lean_ctor_set(x_40, 0, x_123);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_124 = l_Lean_Elab_Term_ensureHasType(x_40, x_112, x_8, x_9, x_10, x_11, x_12, x_13, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_5, x_125, x_8, x_9, x_10, x_11, x_12, x_13, x_126);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = 1;
x_131 = lean_box(x_130);
if (lean_is_scalar(x_129)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_129;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_128);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_133 = lean_ctor_get(x_124, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_135 = x_124;
} else {
 lean_dec_ref(x_124);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_119);
lean_dec(x_112);
lean_free_object(x_40);
lean_inc(x_8);
x_137 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_115);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_6, x_139);
lean_dec(x_6);
x_141 = lean_nat_add(x_7, x_139);
lean_dec(x_7);
x_6 = x_140;
x_7 = x_141;
x_14 = x_138;
goto _start;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_free_object(x_40);
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_143 = lean_ctor_get(x_111, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_111, 1);
lean_inc(x_144);
lean_dec(x_111);
x_145 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_54, x_8, x_9, x_10, x_11, x_12, x_13, x_144);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
 lean_ctor_set_tag(x_148, 1);
}
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_149 = lean_ctor_get(x_40, 0);
lean_inc(x_149);
lean_dec(x_40);
x_150 = lean_st_ref_get(x_13, x_48);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 2);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_take(x_13, x_152);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_155, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 lean_ctor_release(x_155, 2);
 x_159 = x_155;
} else {
 lean_dec_ref(x_155);
 x_159 = lean_box(0);
}
x_160 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 3, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_158);
lean_ctor_set(x_161, 2, x_160);
x_162 = lean_st_ref_set(x_13, x_161, x_156);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_164 = l_Lean_Elab_Term_StructInst_DefaultFields_reduce___main(x_2, x_149, x_10, x_11, x_12, x_13, x_163);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_8);
x_167 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_153, x_8, x_9, x_10, x_11, x_12, x_13, x_166);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = 8192;
x_170 = l_Lean_Expr_FindImpl_initCache;
lean_inc(x_165);
x_171 = l_Lean_Expr_FindImpl_findM_x3f___main___at_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___spec__1(x_169, x_165, x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_173 = l_Lean_Elab_Term_getMVarDecl(x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_168);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 2);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_176);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_178 = l_Lean_Elab_Term_ensureHasType(x_177, x_165, x_8, x_9, x_10, x_11, x_12, x_13, x_175);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = l_Lean_Meta_assignExprMVar___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__2(x_5, x_179, x_8, x_9, x_10, x_11, x_12, x_13, x_180);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_183 = x_181;
} else {
 lean_dec_ref(x_181);
 x_183 = lean_box(0);
}
x_184 = 1;
x_185 = lean_box(x_184);
if (lean_is_scalar(x_183)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_183;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_182);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
x_187 = lean_ctor_get(x_178, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_178, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_189 = x_178;
} else {
 lean_dec_ref(x_178);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_172);
lean_dec(x_165);
lean_inc(x_8);
x_191 = l_Lean_Meta_setMCtx___at_Lean_Elab_Term_savingMCtx___spec__1(x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_168);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_add(x_6, x_193);
lean_dec(x_6);
x_195 = lean_nat_add(x_7, x_193);
lean_dec(x_7);
x_6 = x_194;
x_7 = x_195;
x_14 = x_192;
goto _start;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_38);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_197 = lean_ctor_get(x_164, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_164, 1);
lean_inc(x_198);
lean_dec(x_164);
x_199 = l___private_Lean_Elab_Term_4__liftMetaMFinalizer(x_153, x_8, x_9, x_10, x_11, x_12, x_13, x_198);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
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
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_203 = !lean_is_exclusive(x_39);
if (x_203 == 0)
{
return x_39;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_39, 0);
x_205 = lean_ctor_get(x_39, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_39);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; lean_object* x_208; 
lean_dec(x_34);
lean_dec(x_21);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_6, x_207);
lean_dec(x_6);
x_6 = x_208;
x_14 = x_28;
goto _start;
}
}
}
}
else
{
uint8_t x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_210 = 0;
x_211 = lean_box(x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_14);
return x_212;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
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
x_14 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_1, x_2, x_3, x_4, x_5, x_13, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefault(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_100; 
x_100 = lean_ctor_get(x_1, 2);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
lean_dec(x_1);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_101, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_100);
x_103 = lean_box(0);
x_12 = x_103;
goto block_99;
}
block_99:
{
lean_object* x_13; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_14 = l_PUnit_Inhabited;
x_15 = l_monadInhabited___rarg(x_2, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_inhabited___rarg___boxed), 2, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = l_unreachable_x21___rarg(x_16);
x_18 = lean_apply_9(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
lean_dec(x_13);
x_20 = l_Lean_Elab_Term_StructInst_defaultMissing_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 2)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_24);
x_25 = l_Lean_Elab_Term_isExprMVarAssigned(x_24, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 2);
lean_inc(x_32);
lean_dec(x_3);
x_33 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_1);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_9, 3);
x_36 = l_Lean_replaceRef(x_29, x_35);
lean_dec(x_29);
x_37 = l_Lean_replaceRef(x_36, x_35);
lean_dec(x_36);
x_38 = l_Lean_replaceRef(x_37, x_35);
lean_dec(x_35);
lean_dec(x_37);
lean_ctor_set(x_9, 3, x_38);
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_30, x_31, x_32, x_33, x_24, x_39, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_28);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
if (x_42 == 0)
{
uint8_t x_43; 
lean_dec(x_41);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_40, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_st_ref_take(x_4, x_49);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_set(x_4, x_41, x_51);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = lean_box(0);
lean_ctor_set(x_52, 0, x_55);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_box(0);
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
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_40);
if (x_59 == 0)
{
return x_40;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_40, 0);
x_61 = lean_ctor_get(x_40, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_ctor_get(x_9, 0);
x_64 = lean_ctor_get(x_9, 1);
x_65 = lean_ctor_get(x_9, 2);
x_66 = lean_ctor_get(x_9, 3);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_9);
x_67 = l_Lean_replaceRef(x_29, x_66);
lean_dec(x_29);
x_68 = l_Lean_replaceRef(x_67, x_66);
lean_dec(x_67);
x_69 = l_Lean_replaceRef(x_68, x_66);
lean_dec(x_66);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_tryToSynthesizeDefaultAux___main(x_30, x_31, x_32, x_33, x_24, x_71, x_71, x_5, x_6, x_7, x_8, x_70, x_10, x_28);
lean_dec(x_6);
lean_dec(x_32);
lean_dec(x_30);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_73);
lean_dec(x_4);
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
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
lean_dec(x_72);
x_80 = lean_st_ref_take(x_4, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_set(x_4, x_73, x_81);
lean_dec(x_4);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
x_85 = lean_box(0);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_4);
x_87 = lean_ctor_get(x_72, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_72, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_89 = x_72;
} else {
 lean_dec_ref(x_72);
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
}
else
{
uint8_t x_91; 
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_25);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_25, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set(x_25, 0, x_93);
return x_25;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_25, 1);
lean_inc(x_94);
lean_dec(x_25);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_11);
return x_98;
}
}
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_10(x_13, lean_box(0), x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_3);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__1), 11, 3);
lean_closure_set(x_19, 0, x_16);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_3);
x_20 = lean_alloc_closure((void*)(l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed), 12, 3);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_3);
x_21 = lean_apply_12(x_18, lean_box(0), lean_box(0), x_19, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_20 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_19, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_24 = lean_array_push(x_21, x_1);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
x_26 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_27 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1(x_26, x_15, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_11, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_11, 0, x_30);
return x_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forM___main___at_Lean_Elab_Term_StructInst_DefaultFields_step___main___spec__1___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_step(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_9, 3);
x_13 = l_Lean_replaceRef(x_1, x_12);
x_14 = lean_ctor_get(x_5, 6);
lean_inc(x_14);
lean_inc(x_14);
x_15 = l_Lean_Elab_getBetterRef(x_13, x_14);
lean_dec(x_13);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*8 + 2);
lean_dec(x_5);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_14);
x_17 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_2, x_7, x_8, x_9, x_10, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_17, 1);
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = l_Lean_Elab_addMacroStack(x_2, x_14);
x_26 = l_Lean_addMessageDataContextFull___at_Lean_Meta_Lean_AddMessageDataContext___spec__1(x_25, x_7, x_8, x_9, x_10, x_11);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_15);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set_tag(x_26, 1);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed), 11, 0);
return x_2;
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
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_9, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_17, x_3);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
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
x_19 = lean_box(0);
lean_ctor_set(x_13, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_free_object(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_dec_lt(x_1, x_2);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_20);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_4, 2);
lean_dec(x_23);
lean_inc(x_2);
lean_ctor_set(x_4, 2, x_2);
x_24 = lean_st_ref_take(x_5, x_16);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_st_ref_set(x_5, x_27, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_st_ref_get(x_5, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_2, x_36);
lean_dec(x_2);
x_2 = x_37;
x_12 = x_35;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_unsigned_to_nat(0u);
x_2 = x_40;
x_12 = x_39;
goto _start;
}
}
else
{
uint8_t x_42; 
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
x_42 = !lean_is_exclusive(x_30);
if (x_42 == 0)
{
return x_30;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
x_44 = lean_ctor_get(x_30, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_30);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_4, 0);
x_47 = lean_ctor_get(x_4, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_4);
lean_inc(x_2);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_2);
x_49 = lean_st_ref_take(x_5, x_16);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_48);
lean_inc(x_3);
x_55 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_48, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_5, x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_2, x_61);
lean_dec(x_2);
x_2 = x_62;
x_4 = x_48;
x_12 = x_60;
goto _start;
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_65 = lean_unsigned_to_nat(0u);
x_2 = x_65;
x_4 = x_48;
x_12 = x_64;
goto _start;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_55, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_55, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_69 = x_55;
} else {
 lean_dec_ref(x_55);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_20, 0);
lean_inc(x_71);
x_72 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_20);
lean_dec(x_20);
x_73 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_75 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_71, x_77, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_71);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_13, 0);
x_80 = lean_ctor_get(x_13, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_13);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Elab_Term_StructInst_DefaultFields_findDefaultMissing_x3f___main(x_81, x_3);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
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
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
return x_84;
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_nat_dec_lt(x_1, x_2);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
x_87 = lean_ctor_get(x_4, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 x_89 = x_4;
} else {
 lean_dec_ref(x_4);
 x_89 = lean_box(0);
}
lean_inc(x_2);
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_2);
x_91 = lean_st_ref_take(x_5, x_80);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = 0;
x_94 = lean_box(x_93);
x_95 = lean_st_ref_set(x_5, x_94, x_92);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_90);
lean_inc(x_3);
x_97 = l_Lean_Elab_Term_StructInst_DefaultFields_step___main(x_3, x_90, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_st_ref_get(x_5, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_2, x_103);
lean_dec(x_2);
x_2 = x_104;
x_4 = x_90;
x_12 = x_102;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_2);
x_106 = lean_ctor_get(x_99, 1);
lean_inc(x_106);
lean_dec(x_99);
x_107 = lean_unsigned_to_nat(0u);
x_2 = x_107;
x_4 = x_90;
x_12 = x_106;
goto _start;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_90);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_97, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_97, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_111 = x_97;
} else {
 lean_dec_ref(x_97);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_85, 0);
lean_inc(x_113);
x_114 = l_Lean_Elab_Term_StructInst_DefaultFields_getFieldName(x_85);
lean_dec(x_85);
x_115 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = l_List_foldlM___main___at___private_Lean_Elab_StructInst_12__mkFieldMap___spec__10___closed__3;
x_117 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
x_118 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___closed__3;
x_119 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_113, x_119, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_80);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_113);
return x_120;
}
}
}
}
}
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwErrorAt___at_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Lean_Elab_Term_StructInst_DefaultFields_getHierarchyDepth___main(x_1);
x_10 = l_Array_empty___closed__1;
x_11 = l_Lean_Elab_Term_StructInst_DefaultFields_collectStructNames___main(x_1, x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_st_mk_ref(x_15, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_Elab_Term_StructInst_DefaultFields_propagateLoop___main(x_9, x_12, x_1, x_13, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_17, x_21);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
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
lean_object* l___private_Lean_Elab_StructInst_25__elabStructInstAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_StructInst_5__getStructName___rarg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_75 = lean_st_ref_get(x_9, x_13);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_12);
x_79 = l_Lean_isStructureLike(x_78, x_12);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_12);
x_81 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__3;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l___private_Lean_Elab_StructInst_25__elabStructInstAux___closed__6;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_84, x_4, x_5, x_6, x_7, x_8, x_9, x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
x_14 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_StructInst_7__mkStructView(x_1, x_12, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_21 = l___private_Lean_Elab_StructInst_19__expandStruct___main(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = l___private_Lean_Elab_StructInst_4__elabModifyOp___closed__2;
x_26 = l_Lean_checkTraceOption(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_31, x_4, x_5, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_30);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_30);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_27);
if (x_41 == 0)
{
return x_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_27, 0);
x_43 = lean_ctor_get(x_27, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_27);
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
lean_inc(x_22);
x_45 = l_Lean_Elab_Term_StructInst_formatStruct___main(x_22);
x_46 = lean_box(0);
x_47 = l_Lean_Format_pretty(x_45, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_Elab_logTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_25, x_49, x_4, x_5, x_6, x_7, x_8, x_9, x_23);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l___private_Lean_Elab_StructInst_24__elabStruct___main(x_22, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = l_Lean_Elab_Term_StructInst_DefaultFields_propagate(x_56, x_4, x_5, x_6, x_7, x_8, x_9, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_55);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_52);
if (x_66 == 0)
{
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_21);
if (x_70 == 0)
{
return x_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_21, 0);
x_72 = lean_ctor_get(x_21, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_21);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_11);
if (x_90 == 0)
{
return x_11;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_11, 0);
x_92 = lean_ctor_get(x_11, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_11);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
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
x_13 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__26;
x_14 = lean_array_push(x_13, x_8);
x_15 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__24;
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
x_22 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__22;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__34;
x_25 = lean_array_push(x_23, x_24);
x_26 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_11____closed__20;
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
lean_object* l_Lean_Elab_Term_StructInst_elabStructInst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_85 = l_Lean_Elab_Term_getCurrMacroScope(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_st_ref_get(x_8, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_89, 0);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_st_ref_get(x_4, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_93, 5);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_7, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_7, 2);
lean_inc(x_97);
x_98 = lean_environment_main_module(x_91);
x_99 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_86);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_inc(x_1);
x_100 = l___private_Lean_Elab_StructInst_26__expandStructInstExpectedType(x_1, x_99, x_95);
lean_dec(x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_take(x_4, x_94);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_104, 5);
lean_dec(x_107);
lean_ctor_set(x_104, 5, x_102);
x_108 = lean_st_ref_set(x_4, x_104, x_105);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_10 = x_101;
x_11 = x_109;
goto block_84;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_110 = lean_ctor_get(x_104, 0);
x_111 = lean_ctor_get(x_104, 1);
x_112 = lean_ctor_get(x_104, 2);
x_113 = lean_ctor_get(x_104, 3);
x_114 = lean_ctor_get(x_104, 4);
x_115 = lean_ctor_get(x_104, 6);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_104);
x_116 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_116, 0, x_110);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_112);
lean_ctor_set(x_116, 3, x_113);
lean_ctor_set(x_116, 4, x_114);
lean_ctor_set(x_116, 5, x_102);
lean_ctor_set(x_116, 6, x_115);
x_117 = lean_st_ref_set(x_4, x_116, x_105);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_10 = x_101;
x_11 = x_118;
goto block_84;
}
block_84:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_StructInst_1__expandNonAtomicExplicitSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_StructInst_2__getStructSource(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_StructInst_3__isModifyOp_x3f(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l___private_Lean_Elab_StructInst_25__elabStructInstAux(x_1, x_2, x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_21;
}
else
{
if (lean_obj_tag(x_16) == 2)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = l___private_Lean_Elab_StructInst_4__elabModifyOp(x_1, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_Elab_Term_StructInst_elabStructInst___closed__3;
x_28 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_12, 1);
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_3, 6);
lean_inc(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_3, 6, x_42);
x_43 = 1;
x_44 = l_Lean_Elab_Term_elabTerm(x_38, x_2, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_45 = lean_ctor_get(x_3, 0);
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = lean_ctor_get(x_3, 4);
x_50 = lean_ctor_get(x_3, 5);
x_51 = lean_ctor_get(x_3, 6);
x_52 = lean_ctor_get(x_3, 7);
x_53 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_54 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_55 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_3);
lean_inc(x_38);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
x_58 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_58, 0, x_45);
lean_ctor_set(x_58, 1, x_46);
lean_ctor_set(x_58, 2, x_47);
lean_ctor_set(x_58, 3, x_48);
lean_ctor_set(x_58, 4, x_49);
lean_ctor_set(x_58, 5, x_50);
lean_ctor_set(x_58, 6, x_57);
lean_ctor_set(x_58, 7, x_52);
lean_ctor_set_uint8(x_58, sizeof(void*)*8, x_53);
lean_ctor_set_uint8(x_58, sizeof(void*)*8 + 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*8 + 2, x_55);
x_59 = 1;
x_60 = l_Lean_Elab_Term_elabTerm(x_38, x_2, x_59, x_58, x_4, x_5, x_6, x_7, x_8, x_37);
return x_60;
}
}
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_10, 0);
lean_inc(x_61);
lean_dec(x_10);
x_62 = !lean_is_exclusive(x_3);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_3, 6);
lean_inc(x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_61);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_3, 6, x_65);
x_66 = 1;
x_67 = l_Lean_Elab_Term_elabTerm(x_61, x_2, x_66, x_3, x_4, x_5, x_6, x_7, x_8, x_11);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_68 = lean_ctor_get(x_3, 0);
x_69 = lean_ctor_get(x_3, 1);
x_70 = lean_ctor_get(x_3, 2);
x_71 = lean_ctor_get(x_3, 3);
x_72 = lean_ctor_get(x_3, 4);
x_73 = lean_ctor_get(x_3, 5);
x_74 = lean_ctor_get(x_3, 6);
x_75 = lean_ctor_get(x_3, 7);
x_76 = lean_ctor_get_uint8(x_3, sizeof(void*)*8);
x_77 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 1);
x_78 = lean_ctor_get_uint8(x_3, sizeof(void*)*8 + 2);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_3);
lean_inc(x_61);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_61);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_74);
x_81 = lean_alloc_ctor(0, 8, 3);
lean_ctor_set(x_81, 0, x_68);
lean_ctor_set(x_81, 1, x_69);
lean_ctor_set(x_81, 2, x_70);
lean_ctor_set(x_81, 3, x_71);
lean_ctor_set(x_81, 4, x_72);
lean_ctor_set(x_81, 5, x_73);
lean_ctor_set(x_81, 6, x_80);
lean_ctor_set(x_81, 7, x_75);
lean_ctor_set_uint8(x_81, sizeof(void*)*8, x_76);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 1, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*8 + 2, x_78);
x_82 = 1;
x_83 = l_Lean_Elab_Term_elabTerm(x_61, x_2, x_82, x_81, x_4, x_5, x_6, x_7, x_8, x_11);
return x_83;
}
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Term_StructInst_elabStructInst___closed__1() {
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
x_3 = l_Lean_Elab_Term_quoteAutoTactic___main___closed__2;
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
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__7);
l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8 = _init_l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8();
lean_mark_persistent(l_Array_foldlStepMAux___main___at___private_Lean_Elab_StructInst_3__isModifyOp_x3f___spec__1___closed__8);
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
l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1 = _init_l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1();
lean_mark_persistent(l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__1);
l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2 = _init_l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2();
lean_mark_persistent(l_Array_filterAux___main___at___private_Lean_Elab_StructInst_7__mkStructView___spec__1___closed__2);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
