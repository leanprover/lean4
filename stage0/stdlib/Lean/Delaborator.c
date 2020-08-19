// Lean compiler output
// Module: Lean.Delaborator
// Imports: Init Lean.KeyedDeclsAttribute Lean.ProjFns Lean.Syntax Lean.Elab.Term
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
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_List_firstM___main___at_Lean_Delaborator_delabFor___main___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
extern lean_object* l_Lean_Expr_ctorName___closed__7;
extern lean_object* l_Lean_Name_toString___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withAppFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabOfNat(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withProj(lean_object*);
lean_object* l_Lean_Level_quote___main(lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabProjectionApp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_getExprKind___closed__9;
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___closed__2;
lean_object* l___regBuiltin_Lean_Delaborator_delabFVar___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Delaborator_annotatePos(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_annotatePos___main(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
extern lean_object* l_Lean_mkThunk___closed__1;
lean_object* l_Lean_Delaborator_DelabM_inhabited(lean_object*);
lean_object* l_Lean_Delaborator_getExpr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExpr(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l___regBuiltin_Lean_Delaborator_delabFVar(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__1;
uint8_t l_Lean_getPPCoercions(lean_object*);
lean_object* l_Lean_Delaborator_delab___closed__3;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoeFun(lean_object*);
lean_object* l_Lean_Delaborator_delab(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTraceClass___closed__1;
lean_object* l_Lean_Delaborator_getExprKind___closed__15;
lean_object* l_Lean_Level_quote___main___lambda__2___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withBindingBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1;
lean_object* l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabLam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPBinderTypes___closed__3;
lean_object* l_Lean_Delaborator_getExprKind___closed__1;
lean_object* l_Lean_Delaborator_getExprKind___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureProjections___closed__1;
lean_object* l_Lean_Delaborator_withAppFn(lean_object*);
uint8_t l_Lean_getPPExplicit(lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__3;
lean_object* l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3;
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ppOptions___closed__1;
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__1;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Delaborator_getImplicitParams___closed__1;
extern lean_object* l_Lean_Expr_ctorName___closed__1;
lean_object* l_Lean_Delaborator_withAppArg(lean_object*);
lean_object* l_Lean_Delaborator_delabCoeFun(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_descend___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_tailD___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Level_max___elambda__1___closed__1;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
lean_object* l_Lean_Level_dec___main(lean_object*);
lean_object* l_Lean_Level_quote___main___closed__5;
extern lean_object* l_Lean_Expr_ctorName___closed__2;
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___rarg(lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__10;
lean_object* l_Lean_Delaborator_delabLam___lambda__1___closed__3;
extern lean_object* l_Lean_Expr_ctorName___closed__8;
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Delaborator_hasIdent(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabCoe___closed__1;
lean_object* l_Lean_Delaborator_getExprKind___closed__23;
lean_object* l_Lean_Delaborator_withAppFnArgs___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__4;
lean_object* l_Lean_Delaborator_DelabM_inhabited___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__21;
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_getExprKind___closed__8;
lean_object* l_Lean_Level_quote___main___closed__3;
lean_object* l_Lean_Delaborator_getExprKind___closed__17;
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___closed__4;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1;
lean_object* l___regBuiltin_Lean_Delaborator_delabForall___closed__1;
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
uint8_t l_Lean_getPPStructureProjections(lean_object*);
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___closed__1;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__3;
extern lean_object* l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_getExprKind___closed__4;
lean_object* l_Lean_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabLam___lambda__1___closed__4;
size_t l_USize_shiftRight(size_t, size_t);
extern lean_object* l_Lean_Parser_Term_proj___elambda__1___closed__1;
lean_object* l_Lean_Level_HasQuote___closed__1;
lean_object* l___regBuiltin_Lean_Delaborator_delabOfNat(lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
lean_object* l_Lean_Level_HasQuote;
lean_object* l___regBuiltin_Lean_Delaborator_delabAppImplicit(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabMVar(lean_object*);
lean_object* l_Lean_Delaborator_delabCoe___closed__2;
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1;
lean_object* l_Lean_Delaborator_delabMVar(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__1;
lean_object* l_Lean_Delaborator_delabCoe___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoe___closed__1;
uint8_t l_Lean_getPPUniverses(lean_object*);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__7;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
uint8_t l_Lean_getPPBinderTypes(lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__10;
lean_object* l_Lean_Delaborator_delabSort___closed__3;
lean_object* l_Lean_Delaborator_getExprKind___closed__12;
lean_object* l_Lean_Level_quote___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__1___closed__1;
lean_object* l_Lean_Level_quote___main___closed__6;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__7;
lean_object* l_Lean_Delaborator_annotateCurPos(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___closed__3;
extern lean_object* l_Lean_Parser_Level_imax___elambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__1;
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__13;
lean_object* l_Lean_ppOptions(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__7;
lean_object* l_Lean_Delaborator_delabAppExplicit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabCoe___closed__2;
lean_object* l_Lean_Delaborator_delabSort___closed__10;
extern lean_object* l_Lean_EnvExtension_Inhabited___rarg___closed__1;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__5;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_Delaborator_delabForall___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabFVar(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabLam___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__7;
lean_object* l_Lean_Delaborator_delab___closed__1;
lean_object* l_Lean_Delaborator_getExprKind___closed__20;
lean_object* l_Lean_Level_quote___main___lambda__9___closed__3;
lean_object* l_Lean_Delaborator_delabLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__3;
extern lean_object* l_Lean_Parser_Level_addLit___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_delabLam___lambda__1___closed__1;
extern lean_object* l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
lean_object* l_Lean_Level_quote___main___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__5;
lean_object* l_Lean_Level_quote___main___lambda__4___closed__1;
lean_object* l_Lean_Delaborator_delab___closed__2;
lean_object* l_Lean_Delaborator_delabOfNat___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabAppExplicit(lean_object*);
lean_object* l_Lean_Delaborator_delabLam___closed__1;
lean_object* l_Lean_Delaborator_delabProj___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Delaborator_2__delabBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__5;
lean_object* l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1;
extern lean_object* l_Lean_Unhygienic_MonadQuotation___closed__4;
lean_object* l_Lean_Level_quote___main___closed__2;
lean_object* l_Lean_Delaborator_getExprKind___closed__11;
lean_object* l_Lean_Level_quote___main___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_toNat(lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Term_blockImplicitLambda(lean_object*);
lean_object* l_Lean_Delaborator_delabOfNat___closed__2;
lean_object* l___regBuiltin_Lean_Delaborator_delabLit(lean_object*);
lean_object* l_Lean_Delaborator_delabAttribute___closed__2;
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabForall___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__5;
extern lean_object* l_Std_PersistentArray_Stats_toString___closed__4;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
extern lean_object* l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_delabFor___main(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Delaborator_delabProjectionApp___closed__3;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withAppFnArgs(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_delabLam___lambda__1___closed__2;
extern lean_object* l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
extern lean_object* l_Lean_Expr_ctorName___closed__3;
extern size_t l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
lean_object* l_Lean_Delaborator_getPPOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabForall___closed__1;
extern lean_object* l_Lean_Expr_isCharLit___closed__3;
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_numLitKind___closed__2;
extern lean_object* l_Lean_Meta_commitWhen___lambda__1___closed__1;
lean_object* l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_evalNat___main___closed__6;
lean_object* l_Lean_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_expandArrayLit___closed__9;
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withProj___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Delaborator_delabProjectionApp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1;
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l_Lean_Level_quote___main___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_arrow___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_withBindingDomain(lean_object*);
extern lean_object* l_Lean_Elab_Term_expandArrayLit___closed__8;
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_delabConst___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabProjectionApp(lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___main___rarg(lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__24;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__4;
lean_object* l_Std_mkHashMap___at_Lean_Delaborator_delabAttribute___spec__2(lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__6;
lean_object* l_Lean_Delaborator_delabAttribute___closed__4;
lean_object* l_Lean_Delaborator_getExprKind___closed__7;
lean_object* l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_hasIdent___main___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_FirstTokens_toStr___closed__3;
lean_object* l_Lean_Delaborator_delabAppExplicit___closed__4;
lean_object* l_Lean_Delaborator_getExprKind___closed__19;
lean_object* l_Lean_getPPCoercions___closed__2;
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
lean_object* l_Lean_Delaborator_delabProjectionApp___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_hasIdent___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__6;
lean_object* l_Lean_Delaborator_DelabM_monadQuotation;
lean_object* l_Lean_getPPCoercions___closed__1;
lean_object* l_Lean_Delaborator_delabOfNat___closed__1;
extern lean_object* l_Lean_Parser_Term_explicit___elambda__1___closed__5;
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Level_quote___main___closed__4;
lean_object* l_Lean_getPPCoercions___boxed(lean_object*);
uint8_t l_Lean_Syntax_isAtom(lean_object*);
lean_object* l_Lean_Delaborator_delabCoe___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__6;
lean_object* l_Lean_Delaborator_delabProjectionApp___closed__2;
lean_object* l_Lean_Delaborator_getExprKind___closed__5;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
lean_object* l_Lean_Delaborator_getExprKind___closed__22;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__3;
extern lean_object* l_Lean_Expr_ctorName___closed__9;
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_Parser_Command_openRenamingItem___elambda__1___closed__5;
lean_object* l_Lean_Delaborator_getPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___closed__2;
lean_object* l_Lean_Delaborator_delabSort___closed__2;
extern lean_object* l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabProjectionApp(lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1;
lean_object* l_Lean_delab(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__13;
lean_object* l_Lean_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getPPOption___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__5;
lean_object* l_Lean_Level_quote___main___lambda__1___closed__4;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__2;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__10;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_ppOptions___closed__2;
lean_object* l_Lean_Level_quote___main___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2;
lean_object* l_Lean_Level_quote___main___lambda__9___closed__1;
lean_object* l_Lean_Delaborator_descend(lean_object*);
uint8_t l_Lean_Delaborator_hasIdent___main(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isExplicit(uint8_t);
lean_object* l_Lean_Delaborator_delabMVar___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1;
lean_object* l_Lean_Delaborator_delabMVar___closed__2;
lean_object* l_Lean_Level_quote___main___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__16;
lean_object* l_Lean_Level_quote___main___lambda__4___closed__2;
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__2;
lean_object* l_Lean_Delaborator_delabAttribute___closed__1;
extern lean_object* l_Lean_Parser_Term_prop___elambda__1___closed__5;
lean_object* l_Lean_Level_quote___main___lambda__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getImplicitParams(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2;
lean_object* l_Lean_getPPAll___boxed(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withBindingDomain___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPAll___closed__1;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__1;
lean_object* l_Lean_getPPAll___closed__2;
lean_object* l_Lean_getPPUniverses___closed__1;
lean_object* l_Lean_getPPUniverses___boxed(lean_object*);
lean_object* l_Lean_Delaborator_delabOfNat___closed__3;
lean_object* l_Lean_mkStxStrLit(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__2;
lean_object* l_Lean_Delaborator_delabConst___closed__1;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__1;
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPExplicit___boxed(lean_object*);
lean_object* l_Lean_Delaborator_getExprKind(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__1___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2;
lean_object* lean_mk_syntax_num_lit(lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__8;
lean_object* l___regBuiltin_Lean_Delaborator_delabCoe(lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
lean_object* l_Lean_Delaborator_mkDelabAttribute(lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__9;
lean_object* l_Lean_Name_getRoot___main(lean_object*);
lean_object* l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabLit___closed__1;
lean_object* l_Lean_getPPExplicit___closed__1;
lean_object* l_Lean_Delaborator_getExprKind___closed__6;
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__12;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabSort___closed__1;
lean_object* l___regBuiltin_Lean_Delaborator_delabMVar___closed__1;
lean_object* l_Lean_Delaborator_delabAttribute;
lean_object* l_Lean_Delaborator_delabConst___closed__2;
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__9___closed__2;
extern lean_object* l_Lean_Expr_ctorName___closed__12;
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__4;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5___boxed(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabLam(lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__6;
lean_object* l_Lean_Delaborator_delabSort___closed__8;
lean_object* l___private_Lean_Delaborator_1__shouldGroupWithNext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__4;
lean_object* l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2;
lean_object* l_Lean_Level_quote___main___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabProj(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__1;
lean_object* l_Lean_mkStxLit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___closed__3;
lean_object* l_Lean_Delaborator_getImplicitParams___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withBindingBody(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Lean_Delaborator_descend___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__11;
lean_object* l_Lean_Delaborator_delabProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withAppFnArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__11;
lean_object* l_Lean_Delaborator_withAppArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toArrayAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
lean_object* l_Lean_getPPBinderTypes___closed__2;
lean_object* l_Lean_Delaborator_delabAppExplicit___closed__2;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAttribute___closed__5;
lean_object* l_Lean_Delaborator_delabCoe(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1;
extern lean_object* l_Lean_Parser_Term_sort___elambda__1___closed__4;
lean_object* l_Lean_Delaborator_getImplicitParams___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Delaborator_withAppFnArgs___main(lean_object*);
uint8_t l_Lean_getPPAll(lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__3;
lean_object* l_Lean_Delaborator_delabOfNat___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__18;
lean_object* l_Lean_Delaborator_delabAttribute___closed__3;
lean_object* l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(lean_object*);
lean_object* l_Lean_Delaborator_getExprKind___closed__14;
extern lean_object* l_Lean_mkAppStx___closed__2;
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Delaborator_delabSort___closed__11;
lean_object* l_Lean_Delaborator_delabSort(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureProjections___closed__2;
lean_object* l_Lean_Level_quote(lean_object*);
lean_object* l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Delaborator_2__delabBinders___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabConst___closed__3;
lean_object* l___regBuiltin_Lean_Delaborator_delabForall(lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPBinderTypes___closed__4;
extern lean_object* l_Lean_mkAppStx___closed__1;
lean_object* l_Lean_getPPStructureProjections___boxed(lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2;
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_addParenHeuristic___closed__1;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_mkDelabAttribute___closed__9;
lean_object* l_Lean_getPPBinderTypes___closed__1;
lean_object* l___regBuiltin_Lean_Delaborator_delabProj___closed__1;
lean_object* l_Lean_Delaborator_delabForall(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppImplicit___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_withBindingBody___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Delaborator_delabLam___closed__1;
lean_object* l___regBuiltin_Lean_Delaborator_delabSort(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Delaborator_delabAppExplicit___closed__1;
lean_object* l_Lean_Level_quote___main___lambda__6___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___main___lambda__6___closed__2;
lean_object* l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1;
lean_object* l_Lean_getPPBinderTypes___boxed(lean_object*);
extern lean_object* l_Lean_Elab_Term_tryCoe___closed__3;
lean_object* _init_l_Lean_Level_quote___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("0");
return x_1;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__1___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_numLitKind___closed__2;
x_2 = l_Lean_Level_quote___main___lambda__1___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Level_quote___main___lambda__1___closed__4;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Lean_Level_getLevelOffset___main(x_1);
x_6 = l_Lean_Level_quote___main(x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Lean_Level_quote___main___lambda__2___closed__1;
x_10 = lean_array_push(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Level_getOffsetAux___main(x_1, x_11);
x_13 = lean_mk_syntax_num_lit(x_12);
x_14 = lean_array_push(x_10, x_13);
x_15 = l_Lean_Parser_Level_addLit___elambda__1___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
lean_object* l_Lean_Level_quote___main___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_syntax_num_lit(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__4___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___main___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote___main(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___main___lambda__4___closed__2;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
lean_object* l_Lean_Level_quote___main___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Lean_Level_quote___main(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_10, x_9);
x_12 = l_Lean_nullKind___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Level_quote___main___lambda__4___closed__2;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Level_LevelToFormat_Result_format___main___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__6___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___main___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote___main(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___main___lambda__6___closed__2;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
lean_object* l_Lean_Level_quote___main___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l_Lean_Level_quote___main(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_10, x_9);
x_12 = l_Lean_nullKind___closed__2;
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Level_quote___main___lambda__6___closed__2;
x_15 = lean_array_push(x_14, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
lean_object* l_Lean_Level_quote___main___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_syntax_ident(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_mkHole___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__9___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___lambda__9___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___closed__1;
x_2 = l_Lean_Level_quote___main___lambda__9___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___main___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Level_quote___main___lambda__9___closed__3;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_2 = l_Lean_Level_quote___main___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_quote___main___closed__2;
x_2 = l_Lean_Unhygienic_run___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__9___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_2 = l_Lean_Level_quote___main___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Level_quote___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_quote___main___closed__5;
x_2 = l_Lean_Unhygienic_run___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_quote___main(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_Level_quote___main___closed__3;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Level_toNat(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__2___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_4);
x_7 = l_Lean_Unhygienic_run___rarg(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__3___boxed), 4, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Lean_Unhygienic_run___rarg(x_11);
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_31; uint8_t x_32; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Level_quote___main(x_14);
x_31 = l_Lean_Parser_Level_max___elambda__1___closed__1;
lean_inc(x_15);
x_32 = l_Lean_Syntax_isOfKind(x_15, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = 0;
x_16 = x_33;
goto block_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Syntax_getArgs(x_15);
x_35 = lean_array_get_size(x_34);
lean_dec(x_34);
x_36 = lean_unsigned_to_nat(2u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
x_16 = x_37;
goto block_30;
}
block_30:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_18 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__4___boxed), 6, 3);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_17);
x_19 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Lean_Unhygienic_run___rarg(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_15, x_22);
lean_dec(x_15);
x_24 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_25 = l_Lean_Parser_Level_max___elambda__1___closed__1;
x_26 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__5___boxed), 6, 3);
lean_closure_set(x_26, 0, x_13);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_25);
x_27 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_28 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_28, 0, x_27);
lean_closure_set(x_28, 1, x_26);
x_29 = l_Lean_Unhygienic_run___rarg(x_28);
return x_29;
}
}
}
case 3:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_56; uint8_t x_57; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lean_Level_quote___main(x_39);
x_56 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
lean_inc(x_40);
x_57 = l_Lean_Syntax_isOfKind(x_40, x_56);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = 0;
x_41 = x_58;
goto block_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = l_Lean_Syntax_getArgs(x_40);
x_60 = lean_array_get_size(x_59);
lean_dec(x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_dec_eq(x_60, x_61);
lean_dec(x_60);
x_41 = x_62;
goto block_55;
}
block_55:
{
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_43 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__6___boxed), 6, 3);
lean_closure_set(x_43, 0, x_38);
lean_closure_set(x_43, 1, x_40);
lean_closure_set(x_43, 2, x_42);
x_44 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_45, 0, x_44);
lean_closure_set(x_45, 1, x_43);
x_46 = l_Lean_Unhygienic_run___rarg(x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Lean_Syntax_getArg(x_40, x_47);
lean_dec(x_40);
x_49 = l_Lean_Syntax_getArgs(x_48);
lean_dec(x_48);
x_50 = l_Lean_Parser_Level_imax___elambda__1___closed__1;
x_51 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__7___boxed), 6, 3);
lean_closure_set(x_51, 0, x_38);
lean_closure_set(x_51, 1, x_49);
lean_closure_set(x_51, 2, x_50);
x_52 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_53 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_51);
x_54 = l_Lean_Unhygienic_run___rarg(x_53);
return x_54;
}
}
}
case 4:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_alloc_closure((void*)(l_Lean_Level_quote___main___lambda__8___boxed), 4, 1);
lean_closure_set(x_64, 0, x_63);
x_65 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_66 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___spec__1___rarg), 4, 2);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_64);
x_67 = l_Lean_Unhygienic_run___rarg(x_66);
return x_67;
}
default: 
{
lean_object* x_68; 
lean_dec(x_1);
x_68 = l_Lean_Level_quote___main___closed__6;
return x_68;
}
}
}
}
lean_object* l_Lean_Level_quote___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_quote___main___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_quote___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___main___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Level_quote___main___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___main___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_quote___main___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___main___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Level_quote___main___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___main___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Level_quote___main___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___main___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Level_quote___main___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___main___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Level_quote___main___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___main___lambda__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_quote___main___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_quote___main___lambda__9(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_quote(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Level_quote___main(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Level_HasQuote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Level_HasQuote() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_HasQuote___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_getPPBinderTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pp");
return x_1;
}
}
lean_object* _init_l_Lean_getPPBinderTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_getPPBinderTypes___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPBinderTypes___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binder_types");
return x_1;
}
}
lean_object* _init_l_Lean_getPPBinderTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_getPPBinderTypes___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPBinderTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPBinderTypes___closed__4;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPBinderTypes___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPBinderTypes(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPCoercions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coercions");
return x_1;
}
}
lean_object* _init_l_Lean_getPPCoercions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_getPPCoercions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPCoercions(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPCoercions___closed__2;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPCoercions___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPCoercions(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPExplicit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_Parser_Term_explicit___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPExplicit___closed__1;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPExplicit___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPExplicit(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPStructureProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_projections");
return x_1;
}
}
lean_object* _init_l_Lean_getPPStructureProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_getPPStructureProjections___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPStructureProjections(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPStructureProjections___closed__2;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPStructureProjections___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPStructureProjections(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPUniverses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPUniverses___closed__1;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPUniverses___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPUniverses(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_getPPAll___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("all");
return x_1;
}
}
lean_object* _init_l_Lean_getPPAll___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getPPBinderTypes___closed__2;
x_2 = l_Lean_getPPAll___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPAll(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPAll___closed__2;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPAll___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPAll(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_ppOptions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display implicit arguments");
return x_1;
}
}
lean_object* _init_l_Lean_ppOptions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_registerTraceClass___closed__1;
x_2 = l_Lean_getPPBinderTypes___closed__1;
x_3 = l_Lean_ppOptions___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_ppOptions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPExplicit___closed__1;
x_3 = l_Lean_ppOptions___closed__2;
x_4 = lean_register_option(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
x_7 = lean_box(0);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___rarg), 1, 0);
return x_4;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_inhabited___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
lean_object* l_Lean_Delaborator_DelabM_inhabited(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
return x_2;
}
}
lean_object* l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ReaderT_failure___at_Lean_Delaborator_DelabM_inhabited___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_DelabM_monadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_DelabM_monadQuotation___lambda__1), 5, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Delaborator_DelabM_monadQuotation___closed__1;
x_2 = l_Lean_Delaborator_DelabM_monadQuotation___closed__2;
x_3 = l_Lean_Delaborator_DelabM_monadQuotation___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Delaborator_DelabM_monadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Delaborator_DelabM_monadQuotation___closed__4;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_ReaderT_pure___at_Lean_Delaborator_DelabM_monadQuotation___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid attribute argument, expected identifier");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_attrParamSyntaxToIdentifier(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinDelab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delaborator");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkAppStx___closed__2;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delab");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a delaborator.\n\n[delab k] registers a declaration of type `Lean.Delaborator.Delab` for the `Lean.Expr`\nconstructor `k`. Multiple delaborators for a single constructor are tried in turn until\nthe first success. If the term to be delaborated is an application of a constant `c`,\nelaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")\nto reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`\nis tried first.");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__2;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__4;
x_3 = l_Lean_Delaborator_mkDelabAttribute___closed__9;
x_4 = l_Lean_Delaborator_mkDelabAttribute___closed__8;
x_5 = l_Lean_Delaborator_mkDelabAttribute___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabAttribute");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_mkDelabAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Delaborator_mkDelabAttribute___closed__11;
x_3 = l_Lean_Delaborator_mkDelabAttribute___closed__13;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Delaborator_mkDelabAttribute___lambda__1(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Std_mkHashMap___at_Lean_Delaborator_delabAttribute___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_LocalContext_Inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1;
x_3 = l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabAttribute___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_EnvExtension_Inhabited___rarg___closed__1;
x_3 = l_Lean_Delaborator_delabAttribute___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_Delaborator_delabAttribute___closed__3;
x_2 = lean_box(0);
x_3 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__1;
x_4 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__2;
x_5 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__3;
x_6 = l_Lean_PersistentEnvExtension_inhabited___rarg___closed__4;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Delaborator_delabAttribute___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Delaborator_delabAttribute___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_getExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Delaborator_getExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__3;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_mkAppStx___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__9;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__11;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__13;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__15;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__17;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__19;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__21;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_getExprKind___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_getExprKind___closed__23;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Delaborator_getExprKind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
switch (lean_obj_tag(x_7)) {
case 0:
{
uint8_t x_8; 
lean_free_object(x_5);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = l_Lean_Delaborator_getExprKind___closed__2;
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = l_Lean_Delaborator_getExprKind___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
case 1:
{
uint8_t x_14; 
lean_free_object(x_5);
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = l_Lean_Delaborator_getExprKind___closed__4;
lean_ctor_set(x_4, 0, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = l_Lean_Delaborator_getExprKind___closed__4;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
case 2:
{
uint8_t x_20; 
lean_free_object(x_5);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_4);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_4, 0);
lean_dec(x_21);
x_22 = l_Lean_Delaborator_getExprKind___closed__6;
lean_ctor_set(x_4, 0, x_22);
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = l_Lean_Delaborator_getExprKind___closed__6;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
case 3:
{
uint8_t x_26; 
lean_free_object(x_5);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_4);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_4, 0);
lean_dec(x_27);
x_28 = l_Lean_Delaborator_getExprKind___closed__8;
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = l_Lean_Delaborator_getExprKind___closed__8;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
case 4:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_7, 0);
lean_inc(x_34);
lean_dec(x_7);
x_35 = l_Lean_Delaborator_getExprKind___closed__9;
x_36 = l_Lean_Name_append___main(x_35, x_34);
lean_ctor_set(x_5, 0, x_36);
return x_4;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
lean_dec(x_7);
x_39 = l_Lean_Delaborator_getExprKind___closed__9;
x_40 = l_Lean_Name_append___main(x_39, x_38);
lean_ctor_set(x_5, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
case 5:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_4);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_4, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
lean_dec(x_7);
x_45 = l_Lean_Expr_getAppFn___main(x_44);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 4)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Delaborator_getExprKind___closed__9;
x_48 = l_Lean_Name_append___main(x_47, x_46);
lean_ctor_set(x_5, 0, x_48);
return x_4;
}
else
{
lean_object* x_49; 
lean_dec(x_45);
lean_free_object(x_5);
x_49 = l_Lean_Delaborator_getExprKind___closed__10;
lean_ctor_set(x_4, 0, x_49);
return x_4;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
lean_dec(x_4);
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
lean_dec(x_7);
x_52 = l_Lean_Expr_getAppFn___main(x_51);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 4)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = l_Lean_Delaborator_getExprKind___closed__9;
x_55 = l_Lean_Name_append___main(x_54, x_53);
lean_ctor_set(x_5, 0, x_55);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_5);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_free_object(x_5);
x_57 = l_Lean_Delaborator_getExprKind___closed__10;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
return x_58;
}
}
}
case 6:
{
uint8_t x_59; 
lean_free_object(x_5);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_4);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_4, 0);
lean_dec(x_60);
x_61 = l_Lean_Delaborator_getExprKind___closed__12;
lean_ctor_set(x_4, 0, x_61);
return x_4;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_dec(x_4);
x_63 = l_Lean_Delaborator_getExprKind___closed__12;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
case 7:
{
uint8_t x_65; 
lean_free_object(x_5);
lean_dec(x_7);
x_65 = !lean_is_exclusive(x_4);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_4, 0);
lean_dec(x_66);
x_67 = l_Lean_Delaborator_getExprKind___closed__14;
lean_ctor_set(x_4, 0, x_67);
return x_4;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_4, 1);
lean_inc(x_68);
lean_dec(x_4);
x_69 = l_Lean_Delaborator_getExprKind___closed__14;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
case 8:
{
uint8_t x_71; 
lean_free_object(x_5);
lean_dec(x_7);
x_71 = !lean_is_exclusive(x_4);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_4, 0);
lean_dec(x_72);
x_73 = l_Lean_Delaborator_getExprKind___closed__16;
lean_ctor_set(x_4, 0, x_73);
return x_4;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_4, 1);
lean_inc(x_74);
lean_dec(x_4);
x_75 = l_Lean_Delaborator_getExprKind___closed__16;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
case 9:
{
uint8_t x_77; 
lean_free_object(x_5);
lean_dec(x_7);
x_77 = !lean_is_exclusive(x_4);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_4, 0);
lean_dec(x_78);
x_79 = l_Lean_Delaborator_getExprKind___closed__18;
lean_ctor_set(x_4, 0, x_79);
return x_4;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_4, 1);
lean_inc(x_80);
lean_dec(x_4);
x_81 = l_Lean_Delaborator_getExprKind___closed__18;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
case 10:
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_7, 0);
lean_inc(x_83);
lean_dec(x_7);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; 
lean_free_object(x_5);
x_84 = !lean_is_exclusive(x_4);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_4, 0);
lean_dec(x_85);
x_86 = l_Lean_Delaborator_getExprKind___closed__20;
lean_ctor_set(x_4, 0, x_86);
return x_4;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
lean_dec(x_4);
x_88 = l_Lean_Delaborator_getExprKind___closed__20;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_4);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_4, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
lean_dec(x_90);
x_95 = l_Lean_Delaborator_getExprKind___closed__19;
x_96 = l_Lean_Name_append___main(x_95, x_94);
lean_ctor_set(x_5, 0, x_96);
return x_4;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
lean_dec(x_4);
x_98 = lean_ctor_get(x_90, 0);
lean_inc(x_98);
lean_dec(x_90);
x_99 = l_Lean_Delaborator_getExprKind___closed__19;
x_100 = l_Lean_Name_append___main(x_99, x_98);
lean_ctor_set(x_5, 0, x_100);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_91);
lean_dec(x_90);
lean_free_object(x_5);
x_102 = !lean_is_exclusive(x_4);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_4, 0);
lean_dec(x_103);
x_104 = l_Lean_Delaborator_getExprKind___closed__20;
lean_ctor_set(x_4, 0, x_104);
return x_4;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_4, 1);
lean_inc(x_105);
lean_dec(x_4);
x_106 = l_Lean_Delaborator_getExprKind___closed__20;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
case 11:
{
uint8_t x_108; 
lean_free_object(x_5);
lean_dec(x_7);
x_108 = !lean_is_exclusive(x_4);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_4, 0);
lean_dec(x_109);
x_110 = l_Lean_Delaborator_getExprKind___closed__22;
lean_ctor_set(x_4, 0, x_110);
return x_4;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_4, 1);
lean_inc(x_111);
lean_dec(x_4);
x_112 = l_Lean_Delaborator_getExprKind___closed__22;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
default: 
{
uint8_t x_114; 
lean_free_object(x_5);
lean_dec(x_7);
x_114 = !lean_is_exclusive(x_4);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_4, 0);
lean_dec(x_115);
x_116 = l_Lean_Delaborator_getExprKind___closed__24;
lean_ctor_set(x_4, 0, x_116);
return x_4;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_4, 1);
lean_inc(x_117);
lean_dec(x_4);
x_118 = l_Lean_Delaborator_getExprKind___closed__24;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
}
else
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_5, 0);
lean_inc(x_120);
lean_dec(x_5);
switch (lean_obj_tag(x_120)) {
case 0:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_120);
x_121 = lean_ctor_get(x_4, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_122 = x_4;
} else {
 lean_dec_ref(x_4);
 x_122 = lean_box(0);
}
x_123 = l_Lean_Delaborator_getExprKind___closed__2;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
case 1:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_120);
x_125 = lean_ctor_get(x_4, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_126 = x_4;
} else {
 lean_dec_ref(x_4);
 x_126 = lean_box(0);
}
x_127 = l_Lean_Delaborator_getExprKind___closed__4;
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
case 2:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_120);
x_129 = lean_ctor_get(x_4, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_130 = x_4;
} else {
 lean_dec_ref(x_4);
 x_130 = lean_box(0);
}
x_131 = l_Lean_Delaborator_getExprKind___closed__6;
if (lean_is_scalar(x_130)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_130;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_129);
return x_132;
}
case 3:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_120);
x_133 = lean_ctor_get(x_4, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_134 = x_4;
} else {
 lean_dec_ref(x_4);
 x_134 = lean_box(0);
}
x_135 = l_Lean_Delaborator_getExprKind___closed__8;
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_133);
return x_136;
}
case 4:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_4, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_138 = x_4;
} else {
 lean_dec_ref(x_4);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_120, 0);
lean_inc(x_139);
lean_dec(x_120);
x_140 = l_Lean_Delaborator_getExprKind___closed__9;
x_141 = l_Lean_Name_append___main(x_140, x_139);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
if (lean_is_scalar(x_138)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_138;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_137);
return x_143;
}
case 5:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_4, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_145 = x_4;
} else {
 lean_dec_ref(x_4);
 x_145 = lean_box(0);
}
x_146 = lean_ctor_get(x_120, 0);
lean_inc(x_146);
lean_dec(x_120);
x_147 = l_Lean_Expr_getAppFn___main(x_146);
lean_dec(x_146);
if (lean_obj_tag(x_147) == 4)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_Delaborator_getExprKind___closed__9;
x_150 = l_Lean_Name_append___main(x_149, x_148);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
x_153 = l_Lean_Delaborator_getExprKind___closed__10;
if (lean_is_scalar(x_145)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_145;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_144);
return x_154;
}
}
case 6:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_120);
x_155 = lean_ctor_get(x_4, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_156 = x_4;
} else {
 lean_dec_ref(x_4);
 x_156 = lean_box(0);
}
x_157 = l_Lean_Delaborator_getExprKind___closed__12;
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
case 7:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_120);
x_159 = lean_ctor_get(x_4, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_160 = x_4;
} else {
 lean_dec_ref(x_4);
 x_160 = lean_box(0);
}
x_161 = l_Lean_Delaborator_getExprKind___closed__14;
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_159);
return x_162;
}
case 8:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_120);
x_163 = lean_ctor_get(x_4, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_164 = x_4;
} else {
 lean_dec_ref(x_4);
 x_164 = lean_box(0);
}
x_165 = l_Lean_Delaborator_getExprKind___closed__16;
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
case 9:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_120);
x_167 = lean_ctor_get(x_4, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_168 = x_4;
} else {
 lean_dec_ref(x_4);
 x_168 = lean_box(0);
}
x_169 = l_Lean_Delaborator_getExprKind___closed__18;
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
case 10:
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
lean_dec(x_120);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_4, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_173 = x_4;
} else {
 lean_dec_ref(x_4);
 x_173 = lean_box(0);
}
x_174 = l_Lean_Delaborator_getExprKind___closed__20;
if (lean_is_scalar(x_173)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_173;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_172);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_171, 1);
lean_inc(x_177);
lean_dec(x_171);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_179 = x_4;
} else {
 lean_dec_ref(x_4);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_176, 0);
lean_inc(x_180);
lean_dec(x_176);
x_181 = l_Lean_Delaborator_getExprKind___closed__19;
x_182 = l_Lean_Name_append___main(x_181, x_180);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_179)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_179;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_178);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_177);
lean_dec(x_176);
x_185 = lean_ctor_get(x_4, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_186 = x_4;
} else {
 lean_dec_ref(x_4);
 x_186 = lean_box(0);
}
x_187 = l_Lean_Delaborator_getExprKind___closed__20;
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
}
}
case 11:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_120);
x_189 = lean_ctor_get(x_4, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_190 = x_4;
} else {
 lean_dec_ref(x_4);
 x_190 = lean_box(0);
}
x_191 = l_Lean_Delaborator_getExprKind___closed__22;
if (lean_is_scalar(x_190)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_190;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_189);
return x_192;
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_120);
x_193 = lean_ctor_get(x_4, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_194 = x_4;
} else {
 lean_dec_ref(x_4);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Delaborator_getExprKind___closed__24;
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_193);
return x_196;
}
}
}
}
}
lean_object* l_Lean_Delaborator_getExprKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Delaborator_getExprKind(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
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
lean_object* _init_l_Lean_Delaborator_getPPOption___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_getPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_5);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_getPPAll(x_5);
lean_dec(x_5);
x_11 = l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_box(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_getPPAll(x_16);
lean_dec(x_16);
x_20 = lean_box(x_19);
lean_ctor_set(x_11, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_11);
lean_dec(x_16);
x_22 = l_Lean_Delaborator_getPPOption___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_4);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_24);
x_25 = lean_apply_1(x_1, x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_getPPAll(x_24);
lean_dec(x_24);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
x_31 = l_Lean_Delaborator_getPPOption___closed__1;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_4);
return x_32;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
x_33 = lean_ctor_get(x_2, 3);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_dec(x_2);
x_35 = l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = l_Lean_Delaborator_getPPOption___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
x_40 = lean_apply_1(x_1, x_39);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
x_42 = l_Lean_getPPAll(x_39);
lean_dec(x_39);
x_43 = lean_box(x_42);
lean_ctor_set(x_35, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_4);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_free_object(x_35);
lean_dec(x_39);
x_45 = l_Lean_Delaborator_getPPOption___closed__1;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_ctor_get(x_35, 0);
lean_inc(x_47);
lean_dec(x_35);
lean_inc(x_47);
x_48 = lean_apply_1(x_1, x_47);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_getPPAll(x_47);
lean_dec(x_47);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_4);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_47);
x_54 = l_Lean_Delaborator_getPPOption___closed__1;
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_4);
return x_55;
}
}
}
}
}
}
lean_object* l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___main___at_Lean_Delaborator_getPPOption___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Delaborator_getPPOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_getPPOption(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Delaborator_whenPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_6 = l_Lean_Delaborator_getPPOption(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = lean_apply_3(x_2, x_3, x_4, x_16);
return x_17;
}
}
}
lean_object* l_Lean_Delaborator_whenNotPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_3);
x_6 = l_Lean_Delaborator_getPPOption(x_1, x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_apply_3(x_2, x_3, x_4, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
lean_object* l_Lean_Delaborator_descend___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_mul(x_8, x_10);
lean_dec(x_8);
x_12 = lean_nat_add(x_11, x_2);
lean_dec(x_11);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_1);
x_13 = lean_apply_3(x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_ctor_get(x_4, 2);
x_16 = lean_ctor_get(x_4, 3);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_4);
x_17 = lean_unsigned_to_nat(3u);
x_18 = lean_nat_mul(x_14, x_17);
lean_dec(x_14);
x_19 = lean_nat_add(x_18, x_2);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
x_21 = lean_apply_3(x_3, x_20, x_5, x_6);
return x_21;
}
}
}
lean_object* l_Lean_Delaborator_descend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_descend___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_descend___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Delaborator_descend___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Delaborator_withAppFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Delaborator_getExpr(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Delaborator_descend___rarg(x_9, x_10, x_1, x_2, x_3, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_14 = l_unreachable_x21___rarg(x_13);
x_15 = lean_apply_3(x_14, x_2, x_3, x_12);
return x_15;
}
}
}
lean_object* l_Lean_Delaborator_withAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppFn___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withAppArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Delaborator_getExpr(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Delaborator_descend___rarg(x_9, x_10, x_1, x_2, x_3, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_14 = l_unreachable_x21___rarg(x_13);
x_15 = lean_apply_3(x_14, x_2, x_3, x_12);
return x_15;
}
}
}
lean_object* l_Lean_Delaborator_withAppArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppArg___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withAppFnArgs___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Delaborator_getExpr(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppFnArgs___main___rarg), 5, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Delaborator_withAppFn___rarg(x_10, x_3, x_4, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_apply_1(x_2, x_20);
x_22 = l_Lean_Delaborator_withAppArg___rarg(x_21, x_3, x_4, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_2);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_apply_3(x_1, x_3, x_4, x_27);
return x_28;
}
}
}
lean_object* l_Lean_Delaborator_withAppFnArgs___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppFnArgs___main___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withAppFnArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Delaborator_withAppFnArgs___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Delaborator_withAppFnArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppFnArgs___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withBindingDomain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_Delaborator_getExpr(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_bindingDomain_x21(x_8);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Delaborator_descend___rarg(x_9, x_10, x_1, x_2, x_3, x_7);
return x_11;
}
}
lean_object* l_Lean_Delaborator_withBindingDomain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withBindingDomain___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withBindingBody___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Expr_bindingBody_x21(x_1);
x_8 = lean_expr_instantiate1(x_7, x_4);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Delaborator_descend___rarg(x_8, x_9, x_2, x_3, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Delaborator_withBindingBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_6 = l_Lean_Delaborator_getExpr(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Expr_bindingDomain_x21(x_9);
x_11 = l_Lean_Expr_binderInfo(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Delaborator_withBindingBody___rarg___lambda__1___boxed), 6, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Meta_withLocalDecl___rarg(x_1, x_10, x_11, x_12, x_4, x_8);
return x_13;
}
}
lean_object* l_Lean_Delaborator_withBindingBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withBindingBody___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Delaborator_withBindingBody___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Delaborator_withProj___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Delaborator_getExpr(x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Delaborator_descend___rarg(x_9, x_10, x_1, x_2, x_3, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_14 = l_unreachable_x21___rarg(x_13);
x_15 = lean_apply_3(x_14, x_2, x_3, x_12);
return x_15;
}
}
}
lean_object* l_Lean_Delaborator_withProj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_withProj___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_nat_dec_lt(x_2, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = l_Lean_Syntax_isAtom(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
}
}
}
lean_object* l_Lean_Delaborator_annotatePos___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 1)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
x_57 = !lean_is_exclusive(x_51);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_51, 1);
x_59 = lean_ctor_get(x_51, 0);
lean_dec(x_59);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_52, 1);
x_62 = lean_ctor_get(x_52, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_53);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_53, 1);
x_65 = lean_ctor_get(x_53, 0);
lean_dec(x_65);
x_66 = !lean_is_exclusive(x_54);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_54, 1);
x_68 = lean_ctor_get(x_54, 0);
lean_dec(x_68);
x_69 = l_Lean_mkAppStx___closed__1;
x_70 = lean_string_dec_eq(x_67, x_69);
lean_dec(x_67);
if (x_70 == 0)
{
lean_object* x_71; 
lean_free_object(x_54);
lean_free_object(x_53);
lean_dec(x_64);
lean_free_object(x_52);
lean_dec(x_61);
lean_free_object(x_51);
lean_dec(x_58);
lean_dec(x_56);
x_71 = lean_box(0);
x_3 = x_71;
goto block_50;
}
else
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_2, 1);
lean_dec(x_73);
x_74 = lean_ctor_get(x_2, 0);
lean_dec(x_74);
x_75 = l_Lean_mkAppStx___closed__3;
x_76 = lean_string_dec_eq(x_64, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_ctor_set(x_54, 1, x_69);
lean_inc(x_56);
lean_inc(x_51);
x_77 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_77, x_78);
lean_dec(x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_51);
lean_ctor_set(x_80, 1, x_56);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_box(0);
lean_ctor_set(x_79, 0, x_1);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
lean_ctor_set(x_84, 2, x_83);
x_85 = lean_array_get_size(x_56);
x_86 = lean_nat_dec_lt(x_82, x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_84);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_51);
lean_ctor_set(x_87, 1, x_56);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_array_fget(x_56, x_82);
x_89 = lean_box(0);
x_90 = lean_array_fset(x_56, x_82, x_89);
x_91 = l_Lean_Syntax_setInfo(x_84, x_88);
x_92 = lean_array_fset(x_90, x_82, x_91);
lean_dec(x_82);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_51);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_94 = lean_ctor_get(x_79, 0);
lean_inc(x_94);
lean_dec(x_79);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_1);
x_97 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_95);
x_98 = lean_array_get_size(x_56);
x_99 = lean_nat_dec_lt(x_94, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_97);
lean_dec(x_94);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_51);
lean_ctor_set(x_100, 1, x_56);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_array_fget(x_56, x_94);
x_102 = lean_box(0);
x_103 = lean_array_fset(x_56, x_94, x_102);
x_104 = l_Lean_Syntax_setInfo(x_97, x_101);
x_105 = lean_array_fset(x_103, x_94, x_104);
lean_dec(x_94);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_51);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; uint8_t x_108; 
lean_dec(x_64);
x_107 = l_Lean_mkAppStx___closed__5;
x_108 = lean_string_dec_eq(x_61, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_75);
lean_inc(x_56);
lean_inc(x_51);
x_109 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_110 = lean_unsigned_to_nat(0u);
x_111 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_109, x_110);
lean_dec(x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
lean_dec(x_1);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_51);
lean_ctor_set(x_112, 1, x_56);
return x_112;
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_114 = lean_ctor_get(x_111, 0);
x_115 = lean_box(0);
lean_ctor_set(x_111, 0, x_1);
x_116 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_111);
lean_ctor_set(x_116, 2, x_115);
x_117 = lean_array_get_size(x_56);
x_118 = lean_nat_dec_lt(x_114, x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_116);
lean_dec(x_114);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_51);
lean_ctor_set(x_119, 1, x_56);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_120 = lean_array_fget(x_56, x_114);
x_121 = lean_box(0);
x_122 = lean_array_fset(x_56, x_114, x_121);
x_123 = l_Lean_Syntax_setInfo(x_116, x_120);
x_124 = lean_array_fset(x_122, x_114, x_123);
lean_dec(x_114);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_51);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_126 = lean_ctor_get(x_111, 0);
lean_inc(x_126);
lean_dec(x_111);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_1);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
lean_ctor_set(x_129, 2, x_127);
x_130 = lean_array_get_size(x_56);
x_131 = lean_nat_dec_lt(x_126, x_130);
lean_dec(x_130);
if (x_131 == 0)
{
lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_51);
lean_ctor_set(x_132, 1, x_56);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_array_fget(x_56, x_126);
x_134 = lean_box(0);
x_135 = lean_array_fset(x_56, x_126, x_134);
x_136 = l_Lean_Syntax_setInfo(x_129, x_133);
x_137 = lean_array_fset(x_135, x_126, x_136);
lean_dec(x_126);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_51);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_61);
x_139 = l_Lean_mkAppStx___closed__7;
x_140 = lean_string_dec_eq(x_58, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_75);
lean_ctor_set(x_52, 1, x_107);
lean_inc(x_56);
lean_inc(x_51);
x_141 = l_Lean_Syntax_getArgs(x_2);
lean_dec(x_2);
x_142 = lean_unsigned_to_nat(0u);
x_143 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_141, x_142);
lean_dec(x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
lean_dec(x_1);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_51);
lean_ctor_set(x_144, 1, x_56);
return x_144;
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = lean_ctor_get(x_143, 0);
x_147 = lean_box(0);
lean_ctor_set(x_143, 0, x_1);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_147);
x_149 = lean_array_get_size(x_56);
x_150 = lean_nat_dec_lt(x_146, x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_148);
lean_dec(x_146);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_51);
lean_ctor_set(x_151, 1, x_56);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_array_fget(x_56, x_146);
x_153 = lean_box(0);
x_154 = lean_array_fset(x_56, x_146, x_153);
x_155 = l_Lean_Syntax_setInfo(x_148, x_152);
x_156 = lean_array_fset(x_154, x_146, x_155);
lean_dec(x_146);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_51);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_143, 0);
lean_inc(x_158);
lean_dec(x_143);
x_159 = lean_box(0);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_1);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_161, 2, x_159);
x_162 = lean_array_get_size(x_56);
x_163 = lean_nat_dec_lt(x_158, x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_161);
lean_dec(x_158);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_51);
lean_ctor_set(x_164, 1, x_56);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_array_fget(x_56, x_158);
x_166 = lean_box(0);
x_167 = lean_array_fset(x_56, x_158, x_166);
x_168 = l_Lean_Syntax_setInfo(x_161, x_165);
x_169 = lean_array_fset(x_167, x_158, x_168);
lean_dec(x_158);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_51);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_58);
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_75);
lean_ctor_set(x_52, 1, x_107);
lean_ctor_set(x_51, 1, x_139);
x_171 = lean_array_get_size(x_56);
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_nat_dec_lt(x_172, x_171);
lean_dec(x_171);
if (x_173 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_array_fget(x_56, x_172);
x_175 = lean_box(0);
x_176 = lean_array_fset(x_56, x_172, x_175);
x_177 = l_Lean_Delaborator_annotatePos___main(x_1, x_174);
x_178 = lean_array_fset(x_176, x_172, x_177);
lean_ctor_set(x_2, 1, x_178);
return x_2;
}
}
}
}
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_2);
x_179 = l_Lean_mkAppStx___closed__3;
x_180 = lean_string_dec_eq(x_64, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_ctor_set(x_54, 1, x_69);
lean_inc(x_56);
lean_inc(x_51);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_51);
lean_ctor_set(x_181, 1, x_56);
x_182 = l_Lean_Syntax_getArgs(x_181);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_182, x_183);
lean_dec(x_182);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
lean_dec(x_1);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_51);
lean_ctor_set(x_185, 1, x_56);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 x_187 = x_184;
} else {
 lean_dec_ref(x_184);
 x_187 = lean_box(0);
}
x_188 = lean_box(0);
if (lean_is_scalar(x_187)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_187;
}
lean_ctor_set(x_189, 0, x_1);
x_190 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set(x_190, 2, x_188);
x_191 = lean_array_get_size(x_56);
x_192 = lean_nat_dec_lt(x_186, x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_190);
lean_dec(x_186);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_51);
lean_ctor_set(x_193, 1, x_56);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_array_fget(x_56, x_186);
x_195 = lean_box(0);
x_196 = lean_array_fset(x_56, x_186, x_195);
x_197 = l_Lean_Syntax_setInfo(x_190, x_194);
x_198 = lean_array_fset(x_196, x_186, x_197);
lean_dec(x_186);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_51);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
else
{
lean_object* x_200; uint8_t x_201; 
lean_dec(x_64);
x_200 = l_Lean_mkAppStx___closed__5;
x_201 = lean_string_dec_eq(x_61, x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_179);
lean_inc(x_56);
lean_inc(x_51);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_51);
lean_ctor_set(x_202, 1, x_56);
x_203 = l_Lean_Syntax_getArgs(x_202);
lean_dec(x_202);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_203, x_204);
lean_dec(x_203);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
lean_dec(x_1);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_51);
lean_ctor_set(x_206, 1, x_56);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_207 = lean_ctor_get(x_205, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_box(0);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(1, 1, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_1);
x_211 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
lean_ctor_set(x_211, 2, x_209);
x_212 = lean_array_get_size(x_56);
x_213 = lean_nat_dec_lt(x_207, x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
lean_dec(x_211);
lean_dec(x_207);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_51);
lean_ctor_set(x_214, 1, x_56);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_array_fget(x_56, x_207);
x_216 = lean_box(0);
x_217 = lean_array_fset(x_56, x_207, x_216);
x_218 = l_Lean_Syntax_setInfo(x_211, x_215);
x_219 = lean_array_fset(x_217, x_207, x_218);
lean_dec(x_207);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_51);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; uint8_t x_222; 
lean_dec(x_61);
x_221 = l_Lean_mkAppStx___closed__7;
x_222 = lean_string_dec_eq(x_58, x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_179);
lean_ctor_set(x_52, 1, x_200);
lean_inc(x_56);
lean_inc(x_51);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_51);
lean_ctor_set(x_223, 1, x_56);
x_224 = l_Lean_Syntax_getArgs(x_223);
lean_dec(x_223);
x_225 = lean_unsigned_to_nat(0u);
x_226 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_224, x_225);
lean_dec(x_224);
if (lean_obj_tag(x_226) == 0)
{
lean_object* x_227; 
lean_dec(x_1);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_51);
lean_ctor_set(x_227, 1, x_56);
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_229 = x_226;
} else {
 lean_dec_ref(x_226);
 x_229 = lean_box(0);
}
x_230 = lean_box(0);
if (lean_is_scalar(x_229)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_229;
}
lean_ctor_set(x_231, 0, x_1);
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
lean_ctor_set(x_232, 2, x_230);
x_233 = lean_array_get_size(x_56);
x_234 = lean_nat_dec_lt(x_228, x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_232);
lean_dec(x_228);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_51);
lean_ctor_set(x_235, 1, x_56);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_array_fget(x_56, x_228);
x_237 = lean_box(0);
x_238 = lean_array_fset(x_56, x_228, x_237);
x_239 = l_Lean_Syntax_setInfo(x_232, x_236);
x_240 = lean_array_fset(x_238, x_228, x_239);
lean_dec(x_228);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_51);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; 
lean_dec(x_58);
lean_ctor_set(x_54, 1, x_69);
lean_ctor_set(x_53, 1, x_179);
lean_ctor_set(x_52, 1, x_200);
lean_ctor_set(x_51, 1, x_221);
x_242 = lean_array_get_size(x_56);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_nat_dec_lt(x_243, x_242);
lean_dec(x_242);
if (x_244 == 0)
{
lean_object* x_245; 
lean_dec(x_1);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_51);
lean_ctor_set(x_245, 1, x_56);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_246 = lean_array_fget(x_56, x_243);
x_247 = lean_box(0);
x_248 = lean_array_fset(x_56, x_243, x_247);
x_249 = l_Lean_Delaborator_annotatePos___main(x_1, x_246);
x_250 = lean_array_fset(x_248, x_243, x_249);
x_251 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_251, 0, x_51);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
}
}
}
else
{
lean_object* x_252; size_t x_253; lean_object* x_254; uint8_t x_255; 
x_252 = lean_ctor_get(x_54, 1);
x_253 = lean_ctor_get_usize(x_54, 2);
lean_inc(x_252);
lean_dec(x_54);
x_254 = l_Lean_mkAppStx___closed__1;
x_255 = lean_string_dec_eq(x_252, x_254);
lean_dec(x_252);
if (x_255 == 0)
{
lean_object* x_256; 
lean_free_object(x_53);
lean_dec(x_64);
lean_free_object(x_52);
lean_dec(x_61);
lean_free_object(x_51);
lean_dec(x_58);
lean_dec(x_56);
x_256 = lean_box(0);
x_3 = x_256;
goto block_50;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_257 = x_2;
} else {
 lean_dec_ref(x_2);
 x_257 = lean_box(0);
}
x_258 = l_Lean_mkAppStx___closed__3;
x_259 = lean_string_dec_eq(x_64, x_258);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_260, 0, x_55);
lean_ctor_set(x_260, 1, x_254);
lean_ctor_set_usize(x_260, 2, x_253);
lean_ctor_set(x_53, 0, x_260);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_257)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_257;
}
lean_ctor_set(x_261, 0, x_51);
lean_ctor_set(x_261, 1, x_56);
x_262 = l_Lean_Syntax_getArgs(x_261);
lean_dec(x_261);
x_263 = lean_unsigned_to_nat(0u);
x_264 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_262, x_263);
lean_dec(x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; 
lean_dec(x_1);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_51);
lean_ctor_set(x_265, 1, x_56);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
x_268 = lean_box(0);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 1, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_1);
x_270 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
lean_ctor_set(x_270, 2, x_268);
x_271 = lean_array_get_size(x_56);
x_272 = lean_nat_dec_lt(x_266, x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec(x_270);
lean_dec(x_266);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_51);
lean_ctor_set(x_273, 1, x_56);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_274 = lean_array_fget(x_56, x_266);
x_275 = lean_box(0);
x_276 = lean_array_fset(x_56, x_266, x_275);
x_277 = l_Lean_Syntax_setInfo(x_270, x_274);
x_278 = lean_array_fset(x_276, x_266, x_277);
lean_dec(x_266);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_51);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; uint8_t x_281; 
lean_dec(x_64);
x_280 = l_Lean_mkAppStx___closed__5;
x_281 = lean_string_dec_eq(x_61, x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_282, 0, x_55);
lean_ctor_set(x_282, 1, x_254);
lean_ctor_set_usize(x_282, 2, x_253);
lean_ctor_set(x_53, 1, x_258);
lean_ctor_set(x_53, 0, x_282);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_257)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_257;
}
lean_ctor_set(x_283, 0, x_51);
lean_ctor_set(x_283, 1, x_56);
x_284 = l_Lean_Syntax_getArgs(x_283);
lean_dec(x_283);
x_285 = lean_unsigned_to_nat(0u);
x_286 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_284, x_285);
lean_dec(x_284);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
lean_dec(x_1);
x_287 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_287, 0, x_51);
lean_ctor_set(x_287, 1, x_56);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; 
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
x_290 = lean_box(0);
if (lean_is_scalar(x_289)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_289;
}
lean_ctor_set(x_291, 0, x_1);
x_292 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
lean_ctor_set(x_292, 2, x_290);
x_293 = lean_array_get_size(x_56);
x_294 = lean_nat_dec_lt(x_288, x_293);
lean_dec(x_293);
if (x_294 == 0)
{
lean_object* x_295; 
lean_dec(x_292);
lean_dec(x_288);
x_295 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_295, 0, x_51);
lean_ctor_set(x_295, 1, x_56);
return x_295;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_array_fget(x_56, x_288);
x_297 = lean_box(0);
x_298 = lean_array_fset(x_56, x_288, x_297);
x_299 = l_Lean_Syntax_setInfo(x_292, x_296);
x_300 = lean_array_fset(x_298, x_288, x_299);
lean_dec(x_288);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_51);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; uint8_t x_303; 
lean_dec(x_61);
x_302 = l_Lean_mkAppStx___closed__7;
x_303 = lean_string_dec_eq(x_58, x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_304 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_304, 0, x_55);
lean_ctor_set(x_304, 1, x_254);
lean_ctor_set_usize(x_304, 2, x_253);
lean_ctor_set(x_53, 1, x_258);
lean_ctor_set(x_53, 0, x_304);
lean_ctor_set(x_52, 1, x_280);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_257)) {
 x_305 = lean_alloc_ctor(1, 2, 0);
} else {
 x_305 = x_257;
}
lean_ctor_set(x_305, 0, x_51);
lean_ctor_set(x_305, 1, x_56);
x_306 = l_Lean_Syntax_getArgs(x_305);
lean_dec(x_305);
x_307 = lean_unsigned_to_nat(0u);
x_308 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_306, x_307);
lean_dec(x_306);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; 
lean_dec(x_1);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_51);
lean_ctor_set(x_309, 1, x_56);
return x_309;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_310 = lean_ctor_get(x_308, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 x_311 = x_308;
} else {
 lean_dec_ref(x_308);
 x_311 = lean_box(0);
}
x_312 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_1);
x_314 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
lean_ctor_set(x_314, 2, x_312);
x_315 = lean_array_get_size(x_56);
x_316 = lean_nat_dec_lt(x_310, x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_314);
lean_dec(x_310);
x_317 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_317, 0, x_51);
lean_ctor_set(x_317, 1, x_56);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_318 = lean_array_fget(x_56, x_310);
x_319 = lean_box(0);
x_320 = lean_array_fset(x_56, x_310, x_319);
x_321 = l_Lean_Syntax_setInfo(x_314, x_318);
x_322 = lean_array_fset(x_320, x_310, x_321);
lean_dec(x_310);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_51);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
lean_dec(x_58);
x_324 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_324, 0, x_55);
lean_ctor_set(x_324, 1, x_254);
lean_ctor_set_usize(x_324, 2, x_253);
lean_ctor_set(x_53, 1, x_258);
lean_ctor_set(x_53, 0, x_324);
lean_ctor_set(x_52, 1, x_280);
lean_ctor_set(x_51, 1, x_302);
x_325 = lean_array_get_size(x_56);
x_326 = lean_unsigned_to_nat(0u);
x_327 = lean_nat_dec_lt(x_326, x_325);
lean_dec(x_325);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_1);
if (lean_is_scalar(x_257)) {
 x_328 = lean_alloc_ctor(1, 2, 0);
} else {
 x_328 = x_257;
}
lean_ctor_set(x_328, 0, x_51);
lean_ctor_set(x_328, 1, x_56);
return x_328;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_array_fget(x_56, x_326);
x_330 = lean_box(0);
x_331 = lean_array_fset(x_56, x_326, x_330);
x_332 = l_Lean_Delaborator_annotatePos___main(x_1, x_329);
x_333 = lean_array_fset(x_331, x_326, x_332);
if (lean_is_scalar(x_257)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_257;
}
lean_ctor_set(x_334, 0, x_51);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
}
}
}
else
{
lean_object* x_335; size_t x_336; lean_object* x_337; size_t x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_335 = lean_ctor_get(x_53, 1);
x_336 = lean_ctor_get_usize(x_53, 2);
lean_inc(x_335);
lean_dec(x_53);
x_337 = lean_ctor_get(x_54, 1);
lean_inc(x_337);
x_338 = lean_ctor_get_usize(x_54, 2);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_339 = x_54;
} else {
 lean_dec_ref(x_54);
 x_339 = lean_box(0);
}
x_340 = l_Lean_mkAppStx___closed__1;
x_341 = lean_string_dec_eq(x_337, x_340);
lean_dec(x_337);
if (x_341 == 0)
{
lean_object* x_342; 
lean_dec(x_339);
lean_dec(x_335);
lean_free_object(x_52);
lean_dec(x_61);
lean_free_object(x_51);
lean_dec(x_58);
lean_dec(x_56);
x_342 = lean_box(0);
x_3 = x_342;
goto block_50;
}
else
{
lean_object* x_343; lean_object* x_344; uint8_t x_345; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_343 = x_2;
} else {
 lean_dec_ref(x_2);
 x_343 = lean_box(0);
}
x_344 = l_Lean_mkAppStx___closed__3;
x_345 = lean_string_dec_eq(x_335, x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
if (lean_is_scalar(x_339)) {
 x_346 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_346 = x_339;
}
lean_ctor_set(x_346, 0, x_55);
lean_ctor_set(x_346, 1, x_340);
lean_ctor_set_usize(x_346, 2, x_338);
x_347 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_335);
lean_ctor_set_usize(x_347, 2, x_336);
lean_ctor_set(x_52, 0, x_347);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_343)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_343;
}
lean_ctor_set(x_348, 0, x_51);
lean_ctor_set(x_348, 1, x_56);
x_349 = l_Lean_Syntax_getArgs(x_348);
lean_dec(x_348);
x_350 = lean_unsigned_to_nat(0u);
x_351 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_349, x_350);
lean_dec(x_349);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; 
lean_dec(x_1);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_51);
lean_ctor_set(x_352, 1, x_56);
return x_352;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_354 = x_351;
} else {
 lean_dec_ref(x_351);
 x_354 = lean_box(0);
}
x_355 = lean_box(0);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 1, 0);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_1);
x_357 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
lean_ctor_set(x_357, 2, x_355);
x_358 = lean_array_get_size(x_56);
x_359 = lean_nat_dec_lt(x_353, x_358);
lean_dec(x_358);
if (x_359 == 0)
{
lean_object* x_360; 
lean_dec(x_357);
lean_dec(x_353);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_51);
lean_ctor_set(x_360, 1, x_56);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_361 = lean_array_fget(x_56, x_353);
x_362 = lean_box(0);
x_363 = lean_array_fset(x_56, x_353, x_362);
x_364 = l_Lean_Syntax_setInfo(x_357, x_361);
x_365 = lean_array_fset(x_363, x_353, x_364);
lean_dec(x_353);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_51);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
else
{
lean_object* x_367; uint8_t x_368; 
lean_dec(x_335);
x_367 = l_Lean_mkAppStx___closed__5;
x_368 = lean_string_dec_eq(x_61, x_367);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
if (lean_is_scalar(x_339)) {
 x_369 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_369 = x_339;
}
lean_ctor_set(x_369, 0, x_55);
lean_ctor_set(x_369, 1, x_340);
lean_ctor_set_usize(x_369, 2, x_338);
x_370 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_344);
lean_ctor_set_usize(x_370, 2, x_336);
lean_ctor_set(x_52, 0, x_370);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_343)) {
 x_371 = lean_alloc_ctor(1, 2, 0);
} else {
 x_371 = x_343;
}
lean_ctor_set(x_371, 0, x_51);
lean_ctor_set(x_371, 1, x_56);
x_372 = l_Lean_Syntax_getArgs(x_371);
lean_dec(x_371);
x_373 = lean_unsigned_to_nat(0u);
x_374 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_372, x_373);
lean_dec(x_372);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; 
lean_dec(x_1);
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_51);
lean_ctor_set(x_375, 1, x_56);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; 
x_376 = lean_ctor_get(x_374, 0);
lean_inc(x_376);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 x_377 = x_374;
} else {
 lean_dec_ref(x_374);
 x_377 = lean_box(0);
}
x_378 = lean_box(0);
if (lean_is_scalar(x_377)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_377;
}
lean_ctor_set(x_379, 0, x_1);
x_380 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
lean_ctor_set(x_380, 2, x_378);
x_381 = lean_array_get_size(x_56);
x_382 = lean_nat_dec_lt(x_376, x_381);
lean_dec(x_381);
if (x_382 == 0)
{
lean_object* x_383; 
lean_dec(x_380);
lean_dec(x_376);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_51);
lean_ctor_set(x_383, 1, x_56);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_array_fget(x_56, x_376);
x_385 = lean_box(0);
x_386 = lean_array_fset(x_56, x_376, x_385);
x_387 = l_Lean_Syntax_setInfo(x_380, x_384);
x_388 = lean_array_fset(x_386, x_376, x_387);
lean_dec(x_376);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_51);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
else
{
lean_object* x_390; uint8_t x_391; 
lean_dec(x_61);
x_390 = l_Lean_mkAppStx___closed__7;
x_391 = lean_string_dec_eq(x_58, x_390);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
if (lean_is_scalar(x_339)) {
 x_392 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_392 = x_339;
}
lean_ctor_set(x_392, 0, x_55);
lean_ctor_set(x_392, 1, x_340);
lean_ctor_set_usize(x_392, 2, x_338);
x_393 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_344);
lean_ctor_set_usize(x_393, 2, x_336);
lean_ctor_set(x_52, 1, x_367);
lean_ctor_set(x_52, 0, x_393);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_343)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_343;
}
lean_ctor_set(x_394, 0, x_51);
lean_ctor_set(x_394, 1, x_56);
x_395 = l_Lean_Syntax_getArgs(x_394);
lean_dec(x_394);
x_396 = lean_unsigned_to_nat(0u);
x_397 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_395, x_396);
lean_dec(x_395);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; 
lean_dec(x_1);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_51);
lean_ctor_set(x_398, 1, x_56);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_399 = lean_ctor_get(x_397, 0);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
x_401 = lean_box(0);
if (lean_is_scalar(x_400)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_400;
}
lean_ctor_set(x_402, 0, x_1);
x_403 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
lean_ctor_set(x_403, 2, x_401);
x_404 = lean_array_get_size(x_56);
x_405 = lean_nat_dec_lt(x_399, x_404);
lean_dec(x_404);
if (x_405 == 0)
{
lean_object* x_406; 
lean_dec(x_403);
lean_dec(x_399);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_51);
lean_ctor_set(x_406, 1, x_56);
return x_406;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_407 = lean_array_fget(x_56, x_399);
x_408 = lean_box(0);
x_409 = lean_array_fset(x_56, x_399, x_408);
x_410 = l_Lean_Syntax_setInfo(x_403, x_407);
x_411 = lean_array_fset(x_409, x_399, x_410);
lean_dec(x_399);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_51);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
lean_dec(x_58);
if (lean_is_scalar(x_339)) {
 x_413 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_413 = x_339;
}
lean_ctor_set(x_413, 0, x_55);
lean_ctor_set(x_413, 1, x_340);
lean_ctor_set_usize(x_413, 2, x_338);
x_414 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_344);
lean_ctor_set_usize(x_414, 2, x_336);
lean_ctor_set(x_52, 1, x_367);
lean_ctor_set(x_52, 0, x_414);
lean_ctor_set(x_51, 1, x_390);
x_415 = lean_array_get_size(x_56);
x_416 = lean_unsigned_to_nat(0u);
x_417 = lean_nat_dec_lt(x_416, x_415);
lean_dec(x_415);
if (x_417 == 0)
{
lean_object* x_418; 
lean_dec(x_1);
if (lean_is_scalar(x_343)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_343;
}
lean_ctor_set(x_418, 0, x_51);
lean_ctor_set(x_418, 1, x_56);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_419 = lean_array_fget(x_56, x_416);
x_420 = lean_box(0);
x_421 = lean_array_fset(x_56, x_416, x_420);
x_422 = l_Lean_Delaborator_annotatePos___main(x_1, x_419);
x_423 = lean_array_fset(x_421, x_416, x_422);
if (lean_is_scalar(x_343)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_343;
}
lean_ctor_set(x_424, 0, x_51);
lean_ctor_set(x_424, 1, x_423);
return x_424;
}
}
}
}
}
}
}
else
{
lean_object* x_425; size_t x_426; lean_object* x_427; size_t x_428; lean_object* x_429; lean_object* x_430; size_t x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_425 = lean_ctor_get(x_52, 1);
x_426 = lean_ctor_get_usize(x_52, 2);
lean_inc(x_425);
lean_dec(x_52);
x_427 = lean_ctor_get(x_53, 1);
lean_inc(x_427);
x_428 = lean_ctor_get_usize(x_53, 2);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_429 = x_53;
} else {
 lean_dec_ref(x_53);
 x_429 = lean_box(0);
}
x_430 = lean_ctor_get(x_54, 1);
lean_inc(x_430);
x_431 = lean_ctor_get_usize(x_54, 2);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_432 = x_54;
} else {
 lean_dec_ref(x_54);
 x_432 = lean_box(0);
}
x_433 = l_Lean_mkAppStx___closed__1;
x_434 = lean_string_dec_eq(x_430, x_433);
lean_dec(x_430);
if (x_434 == 0)
{
lean_object* x_435; 
lean_dec(x_432);
lean_dec(x_429);
lean_dec(x_427);
lean_dec(x_425);
lean_free_object(x_51);
lean_dec(x_58);
lean_dec(x_56);
x_435 = lean_box(0);
x_3 = x_435;
goto block_50;
}
else
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_436 = x_2;
} else {
 lean_dec_ref(x_2);
 x_436 = lean_box(0);
}
x_437 = l_Lean_mkAppStx___closed__3;
x_438 = lean_string_dec_eq(x_427, x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
if (lean_is_scalar(x_432)) {
 x_439 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_439 = x_432;
}
lean_ctor_set(x_439, 0, x_55);
lean_ctor_set(x_439, 1, x_433);
lean_ctor_set_usize(x_439, 2, x_431);
if (lean_is_scalar(x_429)) {
 x_440 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_440 = x_429;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_427);
lean_ctor_set_usize(x_440, 2, x_428);
x_441 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_425);
lean_ctor_set_usize(x_441, 2, x_426);
lean_ctor_set(x_51, 0, x_441);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_436)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_436;
}
lean_ctor_set(x_442, 0, x_51);
lean_ctor_set(x_442, 1, x_56);
x_443 = l_Lean_Syntax_getArgs(x_442);
lean_dec(x_442);
x_444 = lean_unsigned_to_nat(0u);
x_445 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_443, x_444);
lean_dec(x_443);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; 
lean_dec(x_1);
x_446 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_446, 0, x_51);
lean_ctor_set(x_446, 1, x_56);
return x_446;
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_449 = lean_box(0);
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_1);
x_451 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
lean_ctor_set(x_451, 2, x_449);
x_452 = lean_array_get_size(x_56);
x_453 = lean_nat_dec_lt(x_447, x_452);
lean_dec(x_452);
if (x_453 == 0)
{
lean_object* x_454; 
lean_dec(x_451);
lean_dec(x_447);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_51);
lean_ctor_set(x_454, 1, x_56);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_455 = lean_array_fget(x_56, x_447);
x_456 = lean_box(0);
x_457 = lean_array_fset(x_56, x_447, x_456);
x_458 = l_Lean_Syntax_setInfo(x_451, x_455);
x_459 = lean_array_fset(x_457, x_447, x_458);
lean_dec(x_447);
x_460 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_460, 0, x_51);
lean_ctor_set(x_460, 1, x_459);
return x_460;
}
}
}
else
{
lean_object* x_461; uint8_t x_462; 
lean_dec(x_427);
x_461 = l_Lean_mkAppStx___closed__5;
x_462 = lean_string_dec_eq(x_425, x_461);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
if (lean_is_scalar(x_432)) {
 x_463 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_463 = x_432;
}
lean_ctor_set(x_463, 0, x_55);
lean_ctor_set(x_463, 1, x_433);
lean_ctor_set_usize(x_463, 2, x_431);
if (lean_is_scalar(x_429)) {
 x_464 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_464 = x_429;
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_437);
lean_ctor_set_usize(x_464, 2, x_428);
x_465 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_425);
lean_ctor_set_usize(x_465, 2, x_426);
lean_ctor_set(x_51, 0, x_465);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_436)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_436;
}
lean_ctor_set(x_466, 0, x_51);
lean_ctor_set(x_466, 1, x_56);
x_467 = l_Lean_Syntax_getArgs(x_466);
lean_dec(x_466);
x_468 = lean_unsigned_to_nat(0u);
x_469 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_467, x_468);
lean_dec(x_467);
if (lean_obj_tag(x_469) == 0)
{
lean_object* x_470; 
lean_dec(x_1);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_51);
lean_ctor_set(x_470, 1, x_56);
return x_470;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
x_471 = lean_ctor_get(x_469, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_469)) {
 lean_ctor_release(x_469, 0);
 x_472 = x_469;
} else {
 lean_dec_ref(x_469);
 x_472 = lean_box(0);
}
x_473 = lean_box(0);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(1, 1, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_1);
x_475 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set(x_475, 2, x_473);
x_476 = lean_array_get_size(x_56);
x_477 = lean_nat_dec_lt(x_471, x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_475);
lean_dec(x_471);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_51);
lean_ctor_set(x_478, 1, x_56);
return x_478;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_479 = lean_array_fget(x_56, x_471);
x_480 = lean_box(0);
x_481 = lean_array_fset(x_56, x_471, x_480);
x_482 = l_Lean_Syntax_setInfo(x_475, x_479);
x_483 = lean_array_fset(x_481, x_471, x_482);
lean_dec(x_471);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_51);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
lean_object* x_485; uint8_t x_486; 
lean_dec(x_425);
x_485 = l_Lean_mkAppStx___closed__7;
x_486 = lean_string_dec_eq(x_58, x_485);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
if (lean_is_scalar(x_432)) {
 x_487 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_487 = x_432;
}
lean_ctor_set(x_487, 0, x_55);
lean_ctor_set(x_487, 1, x_433);
lean_ctor_set_usize(x_487, 2, x_431);
if (lean_is_scalar(x_429)) {
 x_488 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_488 = x_429;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_437);
lean_ctor_set_usize(x_488, 2, x_428);
x_489 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_461);
lean_ctor_set_usize(x_489, 2, x_426);
lean_ctor_set(x_51, 0, x_489);
lean_inc(x_56);
lean_inc(x_51);
if (lean_is_scalar(x_436)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_436;
}
lean_ctor_set(x_490, 0, x_51);
lean_ctor_set(x_490, 1, x_56);
x_491 = l_Lean_Syntax_getArgs(x_490);
lean_dec(x_490);
x_492 = lean_unsigned_to_nat(0u);
x_493 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_491, x_492);
lean_dec(x_491);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; 
lean_dec(x_1);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_51);
lean_ctor_set(x_494, 1, x_56);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_495 = lean_ctor_get(x_493, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 x_496 = x_493;
} else {
 lean_dec_ref(x_493);
 x_496 = lean_box(0);
}
x_497 = lean_box(0);
if (lean_is_scalar(x_496)) {
 x_498 = lean_alloc_ctor(1, 1, 0);
} else {
 x_498 = x_496;
}
lean_ctor_set(x_498, 0, x_1);
x_499 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
lean_ctor_set(x_499, 2, x_497);
x_500 = lean_array_get_size(x_56);
x_501 = lean_nat_dec_lt(x_495, x_500);
lean_dec(x_500);
if (x_501 == 0)
{
lean_object* x_502; 
lean_dec(x_499);
lean_dec(x_495);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_51);
lean_ctor_set(x_502, 1, x_56);
return x_502;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_503 = lean_array_fget(x_56, x_495);
x_504 = lean_box(0);
x_505 = lean_array_fset(x_56, x_495, x_504);
x_506 = l_Lean_Syntax_setInfo(x_499, x_503);
x_507 = lean_array_fset(x_505, x_495, x_506);
lean_dec(x_495);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_51);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; 
lean_dec(x_58);
if (lean_is_scalar(x_432)) {
 x_509 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_509 = x_432;
}
lean_ctor_set(x_509, 0, x_55);
lean_ctor_set(x_509, 1, x_433);
lean_ctor_set_usize(x_509, 2, x_431);
if (lean_is_scalar(x_429)) {
 x_510 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_510 = x_429;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_437);
lean_ctor_set_usize(x_510, 2, x_428);
x_511 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_461);
lean_ctor_set_usize(x_511, 2, x_426);
lean_ctor_set(x_51, 1, x_485);
lean_ctor_set(x_51, 0, x_511);
x_512 = lean_array_get_size(x_56);
x_513 = lean_unsigned_to_nat(0u);
x_514 = lean_nat_dec_lt(x_513, x_512);
lean_dec(x_512);
if (x_514 == 0)
{
lean_object* x_515; 
lean_dec(x_1);
if (lean_is_scalar(x_436)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_436;
}
lean_ctor_set(x_515, 0, x_51);
lean_ctor_set(x_515, 1, x_56);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_516 = lean_array_fget(x_56, x_513);
x_517 = lean_box(0);
x_518 = lean_array_fset(x_56, x_513, x_517);
x_519 = l_Lean_Delaborator_annotatePos___main(x_1, x_516);
x_520 = lean_array_fset(x_518, x_513, x_519);
if (lean_is_scalar(x_436)) {
 x_521 = lean_alloc_ctor(1, 2, 0);
} else {
 x_521 = x_436;
}
lean_ctor_set(x_521, 0, x_51);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
}
}
}
}
else
{
lean_object* x_522; size_t x_523; lean_object* x_524; size_t x_525; lean_object* x_526; lean_object* x_527; size_t x_528; lean_object* x_529; lean_object* x_530; size_t x_531; lean_object* x_532; lean_object* x_533; uint8_t x_534; 
x_522 = lean_ctor_get(x_51, 1);
x_523 = lean_ctor_get_usize(x_51, 2);
lean_inc(x_522);
lean_dec(x_51);
x_524 = lean_ctor_get(x_52, 1);
lean_inc(x_524);
x_525 = lean_ctor_get_usize(x_52, 2);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_526 = x_52;
} else {
 lean_dec_ref(x_52);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_53, 1);
lean_inc(x_527);
x_528 = lean_ctor_get_usize(x_53, 2);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_529 = x_53;
} else {
 lean_dec_ref(x_53);
 x_529 = lean_box(0);
}
x_530 = lean_ctor_get(x_54, 1);
lean_inc(x_530);
x_531 = lean_ctor_get_usize(x_54, 2);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_532 = x_54;
} else {
 lean_dec_ref(x_54);
 x_532 = lean_box(0);
}
x_533 = l_Lean_mkAppStx___closed__1;
x_534 = lean_string_dec_eq(x_530, x_533);
lean_dec(x_530);
if (x_534 == 0)
{
lean_object* x_535; 
lean_dec(x_532);
lean_dec(x_529);
lean_dec(x_527);
lean_dec(x_526);
lean_dec(x_524);
lean_dec(x_522);
lean_dec(x_56);
x_535 = lean_box(0);
x_3 = x_535;
goto block_50;
}
else
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_536 = x_2;
} else {
 lean_dec_ref(x_2);
 x_536 = lean_box(0);
}
x_537 = l_Lean_mkAppStx___closed__3;
x_538 = lean_string_dec_eq(x_527, x_537);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
if (lean_is_scalar(x_532)) {
 x_539 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_539 = x_532;
}
lean_ctor_set(x_539, 0, x_55);
lean_ctor_set(x_539, 1, x_533);
lean_ctor_set_usize(x_539, 2, x_531);
if (lean_is_scalar(x_529)) {
 x_540 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_540 = x_529;
}
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_527);
lean_ctor_set_usize(x_540, 2, x_528);
if (lean_is_scalar(x_526)) {
 x_541 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_541 = x_526;
}
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_524);
lean_ctor_set_usize(x_541, 2, x_525);
x_542 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_522);
lean_ctor_set_usize(x_542, 2, x_523);
lean_inc(x_56);
lean_inc(x_542);
if (lean_is_scalar(x_536)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_536;
}
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_56);
x_544 = l_Lean_Syntax_getArgs(x_543);
lean_dec(x_543);
x_545 = lean_unsigned_to_nat(0u);
x_546 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_544, x_545);
lean_dec(x_544);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
lean_dec(x_1);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_542);
lean_ctor_set(x_547, 1, x_56);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; 
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 x_549 = x_546;
} else {
 lean_dec_ref(x_546);
 x_549 = lean_box(0);
}
x_550 = lean_box(0);
if (lean_is_scalar(x_549)) {
 x_551 = lean_alloc_ctor(1, 1, 0);
} else {
 x_551 = x_549;
}
lean_ctor_set(x_551, 0, x_1);
x_552 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
lean_ctor_set(x_552, 2, x_550);
x_553 = lean_array_get_size(x_56);
x_554 = lean_nat_dec_lt(x_548, x_553);
lean_dec(x_553);
if (x_554 == 0)
{
lean_object* x_555; 
lean_dec(x_552);
lean_dec(x_548);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_542);
lean_ctor_set(x_555, 1, x_56);
return x_555;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_556 = lean_array_fget(x_56, x_548);
x_557 = lean_box(0);
x_558 = lean_array_fset(x_56, x_548, x_557);
x_559 = l_Lean_Syntax_setInfo(x_552, x_556);
x_560 = lean_array_fset(x_558, x_548, x_559);
lean_dec(x_548);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_542);
lean_ctor_set(x_561, 1, x_560);
return x_561;
}
}
}
else
{
lean_object* x_562; uint8_t x_563; 
lean_dec(x_527);
x_562 = l_Lean_mkAppStx___closed__5;
x_563 = lean_string_dec_eq(x_524, x_562);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
if (lean_is_scalar(x_532)) {
 x_564 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_564 = x_532;
}
lean_ctor_set(x_564, 0, x_55);
lean_ctor_set(x_564, 1, x_533);
lean_ctor_set_usize(x_564, 2, x_531);
if (lean_is_scalar(x_529)) {
 x_565 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_565 = x_529;
}
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_537);
lean_ctor_set_usize(x_565, 2, x_528);
if (lean_is_scalar(x_526)) {
 x_566 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_566 = x_526;
}
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_524);
lean_ctor_set_usize(x_566, 2, x_525);
x_567 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_522);
lean_ctor_set_usize(x_567, 2, x_523);
lean_inc(x_56);
lean_inc(x_567);
if (lean_is_scalar(x_536)) {
 x_568 = lean_alloc_ctor(1, 2, 0);
} else {
 x_568 = x_536;
}
lean_ctor_set(x_568, 0, x_567);
lean_ctor_set(x_568, 1, x_56);
x_569 = l_Lean_Syntax_getArgs(x_568);
lean_dec(x_568);
x_570 = lean_unsigned_to_nat(0u);
x_571 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_569, x_570);
lean_dec(x_569);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; 
lean_dec(x_1);
x_572 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_572, 0, x_567);
lean_ctor_set(x_572, 1, x_56);
return x_572;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; uint8_t x_579; 
x_573 = lean_ctor_get(x_571, 0);
lean_inc(x_573);
if (lean_is_exclusive(x_571)) {
 lean_ctor_release(x_571, 0);
 x_574 = x_571;
} else {
 lean_dec_ref(x_571);
 x_574 = lean_box(0);
}
x_575 = lean_box(0);
if (lean_is_scalar(x_574)) {
 x_576 = lean_alloc_ctor(1, 1, 0);
} else {
 x_576 = x_574;
}
lean_ctor_set(x_576, 0, x_1);
x_577 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set(x_577, 1, x_576);
lean_ctor_set(x_577, 2, x_575);
x_578 = lean_array_get_size(x_56);
x_579 = lean_nat_dec_lt(x_573, x_578);
lean_dec(x_578);
if (x_579 == 0)
{
lean_object* x_580; 
lean_dec(x_577);
lean_dec(x_573);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_567);
lean_ctor_set(x_580, 1, x_56);
return x_580;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_581 = lean_array_fget(x_56, x_573);
x_582 = lean_box(0);
x_583 = lean_array_fset(x_56, x_573, x_582);
x_584 = l_Lean_Syntax_setInfo(x_577, x_581);
x_585 = lean_array_fset(x_583, x_573, x_584);
lean_dec(x_573);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_567);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
lean_object* x_587; uint8_t x_588; 
lean_dec(x_524);
x_587 = l_Lean_mkAppStx___closed__7;
x_588 = lean_string_dec_eq(x_522, x_587);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
if (lean_is_scalar(x_532)) {
 x_589 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_589 = x_532;
}
lean_ctor_set(x_589, 0, x_55);
lean_ctor_set(x_589, 1, x_533);
lean_ctor_set_usize(x_589, 2, x_531);
if (lean_is_scalar(x_529)) {
 x_590 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_590 = x_529;
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_537);
lean_ctor_set_usize(x_590, 2, x_528);
if (lean_is_scalar(x_526)) {
 x_591 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_591 = x_526;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_562);
lean_ctor_set_usize(x_591, 2, x_525);
x_592 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_522);
lean_ctor_set_usize(x_592, 2, x_523);
lean_inc(x_56);
lean_inc(x_592);
if (lean_is_scalar(x_536)) {
 x_593 = lean_alloc_ctor(1, 2, 0);
} else {
 x_593 = x_536;
}
lean_ctor_set(x_593, 0, x_592);
lean_ctor_set(x_593, 1, x_56);
x_594 = l_Lean_Syntax_getArgs(x_593);
lean_dec(x_593);
x_595 = lean_unsigned_to_nat(0u);
x_596 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_594, x_595);
lean_dec(x_594);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; 
lean_dec(x_1);
x_597 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_597, 0, x_592);
lean_ctor_set(x_597, 1, x_56);
return x_597;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_598 = lean_ctor_get(x_596, 0);
lean_inc(x_598);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 x_599 = x_596;
} else {
 lean_dec_ref(x_596);
 x_599 = lean_box(0);
}
x_600 = lean_box(0);
if (lean_is_scalar(x_599)) {
 x_601 = lean_alloc_ctor(1, 1, 0);
} else {
 x_601 = x_599;
}
lean_ctor_set(x_601, 0, x_1);
x_602 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
lean_ctor_set(x_602, 2, x_600);
x_603 = lean_array_get_size(x_56);
x_604 = lean_nat_dec_lt(x_598, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; 
lean_dec(x_602);
lean_dec(x_598);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_592);
lean_ctor_set(x_605, 1, x_56);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_606 = lean_array_fget(x_56, x_598);
x_607 = lean_box(0);
x_608 = lean_array_fset(x_56, x_598, x_607);
x_609 = l_Lean_Syntax_setInfo(x_602, x_606);
x_610 = lean_array_fset(x_608, x_598, x_609);
lean_dec(x_598);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_592);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; 
lean_dec(x_522);
if (lean_is_scalar(x_532)) {
 x_612 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_612 = x_532;
}
lean_ctor_set(x_612, 0, x_55);
lean_ctor_set(x_612, 1, x_533);
lean_ctor_set_usize(x_612, 2, x_531);
if (lean_is_scalar(x_529)) {
 x_613 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_613 = x_529;
}
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_537);
lean_ctor_set_usize(x_613, 2, x_528);
if (lean_is_scalar(x_526)) {
 x_614 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_614 = x_526;
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_562);
lean_ctor_set_usize(x_614, 2, x_525);
x_615 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_587);
lean_ctor_set_usize(x_615, 2, x_523);
x_616 = lean_array_get_size(x_56);
x_617 = lean_unsigned_to_nat(0u);
x_618 = lean_nat_dec_lt(x_617, x_616);
lean_dec(x_616);
if (x_618 == 0)
{
lean_object* x_619; 
lean_dec(x_1);
if (lean_is_scalar(x_536)) {
 x_619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_619 = x_536;
}
lean_ctor_set(x_619, 0, x_615);
lean_ctor_set(x_619, 1, x_56);
return x_619;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_620 = lean_array_fget(x_56, x_617);
x_621 = lean_box(0);
x_622 = lean_array_fset(x_56, x_617, x_621);
x_623 = l_Lean_Delaborator_annotatePos___main(x_1, x_620);
x_624 = lean_array_fset(x_622, x_617, x_623);
if (lean_is_scalar(x_536)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_536;
}
lean_ctor_set(x_625, 0, x_615);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
}
}
}
}
}
else
{
lean_object* x_626; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_626 = lean_box(0);
x_3 = x_626;
goto block_50;
}
}
else
{
lean_object* x_627; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_627 = lean_box(0);
x_3 = x_627;
goto block_50;
}
}
else
{
lean_object* x_628; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_628 = lean_box(0);
x_3 = x_628;
goto block_50;
}
}
else
{
lean_object* x_629; 
lean_dec(x_52);
lean_dec(x_51);
x_629 = lean_box(0);
x_3 = x_629;
goto block_50;
}
}
else
{
lean_object* x_630; 
lean_dec(x_51);
x_630 = lean_box(0);
x_3 = x_630;
goto block_50;
}
}
case 3:
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_box(0);
x_632 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_632, 0, x_1);
x_633 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
lean_ctor_set(x_633, 2, x_631);
x_634 = l_Lean_Syntax_setInfo(x_633, x_2);
return x_634;
}
default: 
{
lean_object* x_635; 
x_635 = lean_box(0);
x_3 = x_635;
goto block_50;
}
}
block_50:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = l_Lean_Syntax_getArgs(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_box(0);
lean_ctor_set(x_6, 0, x_1);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_array_get_size(x_10);
x_14 = lean_nat_dec_lt(x_9, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_10, x_9);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_10, x_9, x_16);
x_18 = l_Lean_Syntax_setInfo(x_12, x_15);
x_19 = lean_array_fset(x_17, x_9, x_18);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_19);
return x_2;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_6, 0);
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_23 = lean_box(0);
lean_ctor_set(x_6, 0, x_1);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_array_get_size(x_22);
x_26 = lean_nat_dec_lt(x_20, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_array_fget(x_22, x_20);
x_29 = lean_box(0);
x_30 = lean_array_fset(x_22, x_20, x_29);
x_31 = l_Lean_Syntax_setInfo(x_24, x_28);
x_32 = lean_array_fset(x_30, x_20, x_31);
lean_dec(x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_34 = lean_ctor_get(x_6, 0);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_37 = x_2;
} else {
 lean_dec_ref(x_2);
 x_37 = lean_box(0);
}
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_1);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_38);
x_41 = lean_array_get_size(x_36);
x_42 = lean_nat_dec_lt(x_34, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_34);
if (lean_is_scalar(x_37)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_37;
}
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_array_fget(x_36, x_34);
x_45 = lean_box(0);
x_46 = lean_array_fset(x_36, x_34, x_45);
x_47 = l_Lean_Syntax_setInfo(x_40, x_44);
x_48 = lean_array_fset(x_46, x_34, x_47);
lean_dec(x_34);
if (lean_is_scalar(x_37)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_37;
}
lean_ctor_set(x_49, 0, x_35);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_1);
return x_2;
}
}
}
}
}
lean_object* l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_findIdxAux___main___at_Lean_Delaborator_annotatePos___main___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Delaborator_annotatePos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Delaborator_annotatePos___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_annotateCurPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Delaborator_annotatePos___main(x_5, x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
lean_object* l_Lean_Delaborator_annotateCurPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_annotateCurPos(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_name_eq(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___main___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
}
lean_object* l_List_firstM___main___at_Lean_Delaborator_delabFor___main___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_9 = lean_apply_3(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_1 = x_8;
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
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
}
lean_object* l_Lean_Delaborator_delabFor___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = l_Lean_Delaborator_delabAttribute;
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Lean_PersistentEnvExtension_getState___rarg(x_7, x_5);
lean_dec(x_5);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1(x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_26; 
x_26 = lean_box(0);
x_11 = x_26;
x_12 = x_4;
goto block_25;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_List_firstM___main___at_Lean_Delaborator_delabFor___main___spec__7(x_27, x_2, x_3, x_4);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
x_11 = x_31;
x_12 = x_30;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_2);
x_34 = l_Lean_Delaborator_annotateCurPos(x_33, x_2, x_3, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_11 = x_35;
x_12 = x_36;
goto block_25;
}
}
else
{
uint8_t x_37; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_25:
{
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Name_getRoot___main(x_13);
lean_dec(x_13);
x_1 = x_16;
x_4 = x_12;
goto _start;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_12);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___main___at_Lean_Delaborator_delabFor___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___main___at_Lean_Delaborator_delabFor___main___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___main___at_Lean_Delaborator_delabFor___main___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Delaborator_delabFor___main___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Delaborator_delabFor___main___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_delabFor___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Delaborator_delab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to delaborate '");
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_delab___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_delab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_delab___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Delaborator_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = l_Lean_Delaborator_getExprKind(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Name_toString___closed__1;
lean_inc(x_7);
x_9 = l_Lean_Name_toStringWithSep___main(x_8, x_7);
x_10 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Delaborator_delab___closed__3;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_Core_getConstInfo___closed__5;
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(22, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Delaborator_delabFor___main(x_7, x_1, x_2, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_17);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_18, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_31 = x_19;
} else {
 lean_dec_ref(x_19);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_17);
x_34 = !lean_is_exclusive(x_18);
if (x_34 == 0)
{
return x_18;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_18, 0);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_18);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_Delaborator_delabFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_getLocalDecl(x_9, x_2, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_LocalDecl_userName(x_12);
lean_dec(x_12);
x_14 = lean_mk_syntax_ident(x_13);
lean_ctor_set(x_5, 0, x_14);
lean_ctor_set(x_10, 0, x_5);
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
x_17 = l_Lean_LocalDecl_userName(x_15);
lean_dec(x_15);
x_18 = lean_mk_syntax_ident(x_17);
lean_ctor_set(x_5, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_free_object(x_5);
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
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_5);
lean_dec(x_7);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_26 = l_unreachable_x21___rarg(x_25);
x_27 = lean_apply_3(x_26, x_1, x_2, x_24);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Meta_getLocalDecl(x_30, x_2, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
x_35 = l_Lean_LocalDecl_userName(x_32);
lean_dec(x_32);
x_36 = lean_mk_syntax_ident(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_34)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_34;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_31, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_41 = x_31;
} else {
 lean_dec_ref(x_31);
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
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_28);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
lean_dec(x_4);
x_44 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_45 = l_unreachable_x21___rarg(x_44);
x_46 = lean_apply_3(x_45, x_1, x_2, x_43);
return x_46;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabFVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabFVar), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabFVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__3;
x_4 = l___regBuiltin_Lean_Delaborator_delabFVar___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Delaborator_delabMVar___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_FirstTokens_toStr___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabMVar___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabMVar___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabMVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 2)
{
uint8_t x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_mk_syntax_ident(x_10);
x_12 = l_Lean_Delaborator_delabMVar___closed__2;
x_13 = lean_array_push(x_12, x_11);
x_14 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_5, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_mk_syntax_ident(x_17);
x_19 = l_Lean_Delaborator_delabMVar___closed__2;
x_20 = lean_array_push(x_19, x_18);
x_21 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_5, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_16);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_5);
lean_dec(x_7);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_25 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_26 = l_unreachable_x21___rarg(x_25);
x_27 = lean_apply_3(x_26, x_1, x_2, x_24);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
lean_dec(x_5);
if (lean_obj_tag(x_28) == 2)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_30 = x_4;
} else {
 lean_dec_ref(x_4);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_mk_syntax_ident(x_31);
x_33 = l_Lean_Delaborator_delabMVar___closed__2;
x_34 = lean_array_push(x_33, x_32);
x_35 = l_Lean_Parser_Term_namedHole___elambda__1___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_30)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_30;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_29);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
lean_dec(x_4);
x_40 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_41 = l_unreachable_x21___rarg(x_40);
x_42 = lean_apply_3(x_41, x_1, x_2, x_39);
return x_42;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabMVar___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabMVar), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabMVar(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__5;
x_4 = l___regBuiltin_Lean_Delaborator_delabMVar___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_sort___elambda__1___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabSort___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_prop___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabSort___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_prop___elambda__1___closed__2;
x_2 = l_Lean_Delaborator_delabSort___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_delabSort___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_type___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabSort___closed__7;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabSort___closed__8;
x_2 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_2 = l_Lean_Delaborator_delabSort___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabSort___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Delaborator_delabSort___closed__10;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Delaborator_delabSort(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_7 = x_5;
} else {
 lean_dec_ref(x_5);
 x_7 = lean_box(0);
}
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_9 = x_4;
} else {
 lean_dec_ref(x_4);
 x_9 = lean_box(0);
}
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_24 = l_Lean_Delaborator_delabSort___closed__6;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
case 1:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_27 = l_Lean_Delaborator_delabSort___closed__11;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_26);
x_29 = l_Lean_Level_dec___main(x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_box(0);
x_11 = x_30;
goto block_23;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_29, 0);
x_33 = l_Lean_Level_quote___main(x_32);
x_34 = l_Array_empty___closed__1;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_nullKind___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Delaborator_delabSort___closed__8;
x_39 = lean_array_push(x_38, x_37);
x_40 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_29, 0, x_41);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_29);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_29, 0);
lean_inc(x_43);
lean_dec(x_29);
x_44 = l_Lean_Level_quote___main(x_43);
x_45 = l_Array_empty___closed__1;
x_46 = lean_array_push(x_45, x_44);
x_47 = l_Lean_nullKind___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Delaborator_delabSort___closed__8;
x_50 = lean_array_push(x_49, x_48);
x_51 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
}
}
}
default: 
{
lean_object* x_55; 
x_55 = l_Lean_Level_dec___main(x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_11 = x_56;
goto block_23;
}
else
{
uint8_t x_57; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = l_Lean_Level_quote___main(x_58);
x_60 = l_Array_empty___closed__1;
x_61 = lean_array_push(x_60, x_59);
x_62 = l_Lean_nullKind___closed__2;
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Delaborator_delabSort___closed__8;
x_65 = lean_array_push(x_64, x_63);
x_66 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
lean_ctor_set(x_55, 0, x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_8);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_69 = lean_ctor_get(x_55, 0);
lean_inc(x_69);
lean_dec(x_55);
x_70 = l_Lean_Level_quote___main(x_69);
x_71 = l_Array_empty___closed__1;
x_72 = lean_array_push(x_71, x_70);
x_73 = l_Lean_nullKind___closed__2;
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_Delaborator_delabSort___closed__8;
x_76 = lean_array_push(x_75, x_74);
x_77 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_8);
return x_80;
}
}
}
}
block_23:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_12 = l_Lean_Level_quote___main(x_10);
x_13 = l_Array_empty___closed__1;
x_14 = lean_array_push(x_13, x_12);
x_15 = l_Lean_nullKind___closed__2;
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Delaborator_delabSort___closed__2;
x_18 = lean_array_push(x_17, x_16);
x_19 = l_Lean_Parser_Term_sort___elambda__1___closed__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
if (lean_is_scalar(x_7)) {
 x_21 = lean_alloc_ctor(1, 1, 0);
} else {
 x_21 = x_7;
}
lean_ctor_set(x_21, 0, x_20);
if (lean_is_scalar(x_9)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_9;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_7);
lean_dec(x_6);
x_81 = lean_ctor_get(x_4, 1);
lean_inc(x_81);
lean_dec(x_4);
x_82 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_83 = l_unreachable_x21___rarg(x_82);
x_84 = lean_apply_3(x_83, x_1, x_2, x_81);
return x_84;
}
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabSort___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabSort), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabSort(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__7;
x_4 = l___regBuiltin_Lean_Delaborator_delabSort___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_delabConst___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_Level_quote___main(x_9);
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
lean_object* _init_l_Lean_Delaborator_delabConst___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPUniverses___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabConst___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabConst___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Std_PersistentArray_Stats_toString___closed__4;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabConst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l_Lean_Delaborator_delabConst___closed__1;
x_11 = l_Lean_Delaborator_getPPOption(x_10, x_1, x_2, x_7);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_List_isEmpty___rarg(x_9);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = lean_unbox(x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_9);
x_18 = lean_mk_syntax_ident(x_8);
lean_ctor_set(x_13, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_19 = lean_mk_syntax_ident(x_8);
x_20 = l_Array_empty___closed__1;
x_21 = lean_array_push(x_20, x_19);
x_22 = l_Lean_Delaborator_delabConst___closed__2;
x_23 = lean_array_push(x_21, x_22);
x_24 = l_List_redLength___main___rarg(x_9);
x_25 = lean_mk_empty_array_with_capacity(x_24);
lean_dec(x_24);
x_26 = l_List_toArrayAux___main___rarg(x_9, x_25);
x_27 = x_26;
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_umapMAux___main___at_Lean_Delaborator_delabConst___spec__1(x_28, x_27);
x_30 = x_29;
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_30, x_30, x_28, x_20);
lean_dec(x_30);
x_32 = l_Lean_nullKind___closed__2;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_array_push(x_23, x_33);
x_35 = l_Lean_Delaborator_delabConst___closed__3;
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_13, 0, x_38);
return x_11;
}
}
else
{
lean_object* x_39; 
lean_dec(x_15);
lean_dec(x_9);
x_39 = lean_mk_syntax_ident(x_8);
lean_ctor_set(x_13, 0, x_39);
return x_11;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_13, 0);
lean_inc(x_40);
lean_dec(x_13);
x_41 = l_List_isEmpty___rarg(x_9);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = lean_unbox(x_40);
lean_dec(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
x_43 = lean_mk_syntax_ident(x_8);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_11, 0, x_44);
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_45 = lean_mk_syntax_ident(x_8);
x_46 = l_Array_empty___closed__1;
x_47 = lean_array_push(x_46, x_45);
x_48 = l_Lean_Delaborator_delabConst___closed__2;
x_49 = lean_array_push(x_47, x_48);
x_50 = l_List_redLength___main___rarg(x_9);
x_51 = lean_mk_empty_array_with_capacity(x_50);
lean_dec(x_50);
x_52 = l_List_toArrayAux___main___rarg(x_9, x_51);
x_53 = x_52;
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_umapMAux___main___at_Lean_Delaborator_delabConst___spec__1(x_54, x_53);
x_56 = x_55;
x_57 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_56, x_56, x_54, x_46);
lean_dec(x_56);
x_58 = l_Lean_nullKind___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_array_push(x_49, x_59);
x_61 = l_Lean_Delaborator_delabConst___closed__3;
x_62 = lean_array_push(x_60, x_61);
x_63 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_11, 0, x_65);
return x_11;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_40);
lean_dec(x_9);
x_66 = lean_mk_syntax_ident(x_8);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_11, 0, x_67);
return x_11;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_68 = lean_ctor_get(x_11, 0);
x_69 = lean_ctor_get(x_11, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_11);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
x_72 = l_List_isEmpty___rarg(x_9);
if (x_72 == 0)
{
uint8_t x_73; 
x_73 = lean_unbox(x_70);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_9);
x_74 = lean_mk_syntax_ident(x_8);
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_77 = lean_mk_syntax_ident(x_8);
x_78 = l_Array_empty___closed__1;
x_79 = lean_array_push(x_78, x_77);
x_80 = l_Lean_Delaborator_delabConst___closed__2;
x_81 = lean_array_push(x_79, x_80);
x_82 = l_List_redLength___main___rarg(x_9);
x_83 = lean_mk_empty_array_with_capacity(x_82);
lean_dec(x_82);
x_84 = l_List_toArrayAux___main___rarg(x_9, x_83);
x_85 = x_84;
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Array_umapMAux___main___at_Lean_Delaborator_delabConst___spec__1(x_86, x_85);
x_88 = x_87;
x_89 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_88, x_88, x_86, x_78);
lean_dec(x_88);
x_90 = l_Lean_nullKind___closed__2;
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_push(x_81, x_91);
x_93 = l_Lean_Delaborator_delabConst___closed__3;
x_94 = lean_array_push(x_92, x_93);
x_95 = l_Lean_Parser_Term_explicitUniv___elambda__1___closed__2;
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
if (lean_is_scalar(x_71)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_71;
}
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_69);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_70);
lean_dec(x_9);
x_99 = lean_mk_syntax_ident(x_8);
if (lean_is_scalar(x_71)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_71;
}
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_69);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_6);
x_102 = lean_ctor_get(x_4, 1);
lean_inc(x_102);
lean_dec(x_4);
x_103 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_104 = l_unreachable_x21___rarg(x_103);
x_105 = lean_apply_3(x_104, x_1, x_2, x_102);
return x_105;
}
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = x_2;
return x_3;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = x_2;
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = l_Lean_Expr_fvarId_x21(x_12);
lean_dec(x_12);
lean_inc(x_3);
x_14 = l_Lean_Meta_getLocalDecl(x_13, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_LocalDecl_binderInfo(x_15);
lean_dec(x_15);
x_18 = l_Lean_BinderInfo_isExplicit(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1;
x_22 = lean_array_fset(x_11, x_1, x_21);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_1, x_24);
x_26 = l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2;
x_27 = lean_array_fset(x_11, x_1, x_26);
lean_dec(x_1);
x_1 = x_25;
x_2 = x_27;
x_4 = x_16;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l_Lean_Delaborator_getImplicitParams___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
x_9 = lean_apply_2(x_8, x_3, x_4);
return x_9;
}
}
lean_object* _init_l_Lean_Delaborator_getImplicitParams___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_getImplicitParams___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_getImplicitParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Delaborator_getImplicitParams___closed__1;
x_8 = l_Lean_Meta_forallTelescopeReducing___rarg(x_5, x_7, x_2, x_6);
return x_8;
}
else
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Delaborator_getImplicitParams___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_getImplicitParams___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
x_4 = x_10;
goto _start;
}
else
{
lean_dec(x_4);
return x_8;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_apply_3(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_apply_4(x_2, x_15, x_3, x_4, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 0);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_explicit___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_69; 
x_69 = l_Lean_Expr_isConst(x_1);
if (x_69 == 0)
{
lean_object* x_70; 
lean_inc(x_3);
x_70 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_5 = x_71;
x_6 = x_72;
goto block_68;
}
else
{
uint8_t x_73; 
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_inc(x_3);
x_77 = l_Lean_Delaborator_delabConst(x_2, x_3, x_4);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_5 = x_78;
x_6 = x_79;
goto block_68;
}
else
{
uint8_t x_80; 
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_77);
if (x_80 == 0)
{
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
block_68:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_6);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_array_get_size(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(x_13, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Array_empty___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_5, 0, x_18);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2;
x_20 = lean_array_push(x_19, x_10);
x_21 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Array_empty___closed__1;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_5, 0, x_24);
lean_ctor_set(x_11, 0, x_5);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_array_get_size(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(x_25, x_25, x_27, x_28);
lean_dec(x_27);
lean_dec(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = l_Array_empty___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_5, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2;
x_34 = lean_array_push(x_33, x_10);
x_35 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Array_empty___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_5, 0, x_38);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_5);
lean_ctor_set(x_39, 1, x_26);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_5);
lean_dec(x_10);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
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
x_44 = lean_ctor_get(x_5, 0);
lean_inc(x_44);
lean_dec(x_5);
x_45 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_6);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
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
x_49 = lean_array_get_size(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(x_46, x_46, x_49, x_50);
lean_dec(x_49);
lean_dec(x_46);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = l_Array_empty___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
if (lean_is_scalar(x_48)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_48;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_47);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2;
x_57 = lean_array_push(x_56, x_44);
x_58 = l_Lean_Parser_Term_explicit___elambda__1___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Array_empty___closed__1;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_48)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_48;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_47);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_44);
x_64 = lean_ctor_get(x_45, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_45, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_66 = x_45;
} else {
 lean_dec_ref(x_45);
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
}
}
}
}
}
lean_object* l_Lean_Delaborator_delabAppExplicit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
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
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 0);
x_20 = lean_array_push(x_7, x_19);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_9, 0, x_1);
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
lean_dec(x_9);
x_22 = lean_array_push(x_7, x_21);
lean_ctor_set(x_1, 1, x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_8, 0, x_23);
return x_8;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_dec(x_8);
x_25 = lean_ctor_get(x_9, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_26 = x_9;
} else {
 lean_dec_ref(x_9);
 x_26 = lean_box(0);
}
x_27 = lean_array_push(x_7, x_25);
lean_ctor_set(x_1, 1, x_27);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_free_object(x_1);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_36 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_35);
lean_dec(x_34);
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
x_40 = lean_box(0);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_43 = x_36;
} else {
 lean_dec_ref(x_36);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
x_46 = lean_array_push(x_35, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_43)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_43;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_34);
x_50 = lean_ctor_get(x_36, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_52 = x_36;
} else {
 lean_dec_ref(x_36);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_getExpr___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppExplicit___lambda__1), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppExplicit___closed__1;
x_2 = l_Lean_Delaborator_delabAppExplicit___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppExplicit___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppExplicit___lambda__2), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabAppExplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabAppExplicit___closed__3;
x_5 = l_Lean_Delaborator_delabAppExplicit___closed__4;
x_6 = l_Lean_Delaborator_withAppFnArgs___main___rarg(x_4, x_5, x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Array_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = l_Array_empty___closed__1;
x_22 = lean_array_push(x_21, x_18);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_19, x_19, x_23, x_21);
lean_dec(x_19);
x_25 = l_Lean_nullKind___closed__2;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_push(x_22, x_26);
x_28 = l_Lean_mkAppStx___closed__8;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_7, 0, x_29);
return x_6;
}
else
{
lean_dec(x_19);
lean_ctor_set(x_7, 0, x_18);
return x_6;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l_Array_isEmpty___rarg(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = l_Array_empty___closed__1;
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_33, x_33, x_37, x_35);
lean_dec(x_33);
x_39 = l_Lean_nullKind___closed__2;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = lean_array_push(x_36, x_40);
x_42 = l_Lean_mkAppStx___closed__8;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_7, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_33);
lean_ctor_set(x_7, 0, x_32);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_7);
lean_ctor_set(x_45, 1, x_31);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_7, 0);
lean_inc(x_46);
lean_dec(x_7);
x_47 = lean_ctor_get(x_6, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_48 = x_6;
} else {
 lean_dec_ref(x_6);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = l_Array_isEmpty___rarg(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_49);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_50, x_50, x_54, x_52);
lean_dec(x_50);
x_56 = l_Lean_nullKind___closed__2;
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_array_push(x_53, x_57);
x_59 = l_Lean_mkAppStx___closed__8;
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
if (lean_is_scalar(x_48)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_48;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_47);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_50);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_49);
if (lean_is_scalar(x_48)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_48;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_47);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_6);
if (x_65 == 0)
{
return x_6;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_6, 0);
x_67 = lean_ctor_get(x_6, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_6);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabAppExplicit___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppExplicit), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabAppExplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__9;
x_4 = l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Expr_isConst(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Array_toList___rarg(x_19);
lean_dec(x_19);
x_21 = l_Array_empty___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_7, 0, x_23);
lean_ctor_set(x_17, 0, x_7);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = l_Array_toList___rarg(x_24);
lean_dec(x_24);
x_27 = l_Array_empty___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_7, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_7);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_free_object(x_7);
lean_dec(x_16);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
return x_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_17, 0);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_17);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_7, 0);
lean_inc(x_35);
lean_dec(x_7);
x_36 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_14);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
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
x_40 = l_Array_toList___rarg(x_37);
lean_dec(x_37);
x_41 = l_Array_empty___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_35);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_39)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_39;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_48 = x_36;
} else {
 lean_dec_ref(x_36);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_6);
if (x_50 == 0)
{
return x_6;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_6, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; 
lean_inc(x_3);
x_54 = l_Lean_Delaborator_delabConst(x_2, x_3, x_4);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 0);
lean_dec(x_57);
x_58 = lean_box(0);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_54, 1);
lean_inc(x_62);
lean_dec(x_54);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_55, 0);
x_65 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_62);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = l_Array_toList___rarg(x_67);
lean_dec(x_67);
x_69 = l_Array_empty___closed__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_64);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_55, 0, x_71);
lean_ctor_set(x_65, 0, x_55);
return x_65;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_65, 0);
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_65);
x_74 = l_Array_toList___rarg(x_72);
lean_dec(x_72);
x_75 = l_Array_empty___closed__1;
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_64);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_55, 0, x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_55);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_free_object(x_55);
lean_dec(x_64);
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
return x_65;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_ctor_get(x_65, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_65);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_55, 0);
lean_inc(x_83);
lean_dec(x_55);
x_84 = l_Lean_Delaborator_getImplicitParams(x_1, x_3, x_62);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = l_Array_toList___rarg(x_85);
lean_dec(x_85);
x_89 = l_Array_empty___closed__1;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_87)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_87;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_86);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_83);
x_94 = lean_ctor_get(x_84, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
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
}
else
{
uint8_t x_98; 
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_54);
if (x_98 == 0)
{
return x_54;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_54, 0);
x_100 = lean_ctor_get(x_54, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_54);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get(x_5, 0);
lean_dec(x_12);
x_13 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_free_object(x_5);
lean_dec(x_11);
lean_free_object(x_1);
lean_dec(x_8);
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
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = l_List_tailD___rarg(x_6, x_6);
x_26 = lean_array_push(x_11, x_24);
lean_ctor_set(x_5, 1, x_26);
lean_ctor_set(x_5, 0, x_25);
lean_ctor_set(x_14, 0, x_1);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_List_tailD___rarg(x_6, x_6);
x_29 = lean_array_push(x_11, x_27);
lean_ctor_set(x_5, 1, x_29);
lean_ctor_set(x_5, 0, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
x_34 = l_List_tailD___rarg(x_6, x_6);
x_35 = lean_array_push(x_11, x_32);
lean_ctor_set(x_5, 1, x_35);
lean_ctor_set(x_5, 0, x_34);
if (lean_is_scalar(x_33)) {
 x_36 = lean_alloc_ctor(1, 1, 0);
} else {
 x_36 = x_33;
}
lean_ctor_set(x_36, 0, x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_free_object(x_5);
lean_dec(x_11);
lean_free_object(x_1);
lean_dec(x_8);
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
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_5, 1);
lean_inc(x_42);
lean_dec(x_5);
x_43 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_free_object(x_1);
lean_dec(x_8);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
 x_52 = lean_box(0);
}
x_53 = l_List_tailD___rarg(x_6, x_6);
x_54 = lean_array_push(x_42, x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_1, 1, x_55);
if (lean_is_scalar(x_52)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_52;
}
lean_ctor_set(x_56, 0, x_1);
if (lean_is_scalar(x_50)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_50;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_49);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_42);
lean_free_object(x_1);
lean_dec(x_8);
x_58 = lean_ctor_get(x_43, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_43, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_60 = x_43;
} else {
 lean_dec_ref(x_43);
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
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_ctor_get(x_5, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_64 = x_5;
} else {
 lean_dec_ref(x_5);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
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
x_69 = lean_box(0);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_74 = x_66;
} else {
 lean_dec_ref(x_66);
 x_74 = lean_box(0);
}
x_75 = l_List_tailD___rarg(x_6, x_6);
x_76 = lean_array_push(x_63, x_73);
if (lean_is_scalar(x_64)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_64;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_62);
lean_ctor_set(x_78, 1, x_77);
if (lean_is_scalar(x_74)) {
 x_79 = lean_alloc_ctor(1, 1, 0);
} else {
 x_79 = x_74;
}
lean_ctor_set(x_79, 0, x_78);
if (lean_is_scalar(x_72)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_72;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_71);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
x_81 = lean_ctor_get(x_65, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
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
}
else
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_6, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_1);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
lean_dec(x_89);
x_90 = !lean_is_exclusive(x_5);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_5, 1);
x_92 = lean_ctor_get(x_5, 0);
lean_dec(x_92);
x_93 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_free_object(x_5);
lean_dec(x_91);
lean_free_object(x_1);
lean_dec(x_88);
lean_dec(x_6);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_93);
if (x_101 == 0)
{
lean_object* x_102; uint8_t x_103; 
x_102 = lean_ctor_get(x_93, 0);
lean_dec(x_102);
x_103 = !lean_is_exclusive(x_94);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_94, 0);
x_105 = lean_box(0);
x_106 = l_List_tailD___rarg(x_6, x_105);
lean_dec(x_6);
x_107 = lean_array_push(x_91, x_104);
lean_ctor_set(x_5, 1, x_107);
lean_ctor_set(x_5, 0, x_106);
lean_ctor_set(x_94, 0, x_1);
return x_93;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_94, 0);
lean_inc(x_108);
lean_dec(x_94);
x_109 = lean_box(0);
x_110 = l_List_tailD___rarg(x_6, x_109);
lean_dec(x_6);
x_111 = lean_array_push(x_91, x_108);
lean_ctor_set(x_5, 1, x_111);
lean_ctor_set(x_5, 0, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_93, 0, x_112);
return x_93;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_113 = lean_ctor_get(x_93, 1);
lean_inc(x_113);
lean_dec(x_93);
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_115 = x_94;
} else {
 lean_dec_ref(x_94);
 x_115 = lean_box(0);
}
x_116 = lean_box(0);
x_117 = l_List_tailD___rarg(x_6, x_116);
lean_dec(x_6);
x_118 = lean_array_push(x_91, x_114);
lean_ctor_set(x_5, 1, x_118);
lean_ctor_set(x_5, 0, x_117);
if (lean_is_scalar(x_115)) {
 x_119 = lean_alloc_ctor(1, 1, 0);
} else {
 x_119 = x_115;
}
lean_ctor_set(x_119, 0, x_1);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_113);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_free_object(x_5);
lean_dec(x_91);
lean_free_object(x_1);
lean_dec(x_88);
lean_dec(x_6);
x_121 = !lean_is_exclusive(x_93);
if (x_121 == 0)
{
return x_93;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_93, 0);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_93);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_5, 1);
lean_inc(x_125);
lean_dec(x_5);
x_126 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_125);
lean_free_object(x_1);
lean_dec(x_88);
lean_dec(x_6);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_129 = x_126;
} else {
 lean_dec_ref(x_126);
 x_129 = lean_box(0);
}
x_130 = lean_box(0);
if (lean_is_scalar(x_129)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_129;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_128);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_132 = lean_ctor_get(x_126, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_133 = x_126;
} else {
 lean_dec_ref(x_126);
 x_133 = lean_box(0);
}
x_134 = lean_ctor_get(x_127, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_135 = x_127;
} else {
 lean_dec_ref(x_127);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
x_137 = l_List_tailD___rarg(x_6, x_136);
lean_dec(x_6);
x_138 = lean_array_push(x_125, x_134);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
lean_ctor_set(x_1, 1, x_139);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_1);
if (lean_is_scalar(x_133)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_133;
}
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_132);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_125);
lean_free_object(x_1);
lean_dec(x_88);
lean_dec(x_6);
x_142 = lean_ctor_get(x_126, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_144 = x_126;
} else {
 lean_dec_ref(x_126);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
lean_dec(x_1);
x_147 = lean_ctor_get(x_5, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_148 = x_5;
} else {
 lean_dec_ref(x_5);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Delaborator_delab(x_2, x_3, x_4);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_6);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_box(0);
if (lean_is_scalar(x_152)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_152;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_151);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_150, 0);
lean_inc(x_157);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 x_158 = x_150;
} else {
 lean_dec_ref(x_150);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
x_160 = l_List_tailD___rarg(x_6, x_159);
lean_dec(x_6);
x_161 = lean_array_push(x_147, x_157);
if (lean_is_scalar(x_148)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_148;
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_146);
lean_ctor_set(x_163, 1, x_162);
if (lean_is_scalar(x_158)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_158;
}
lean_ctor_set(x_164, 0, x_163);
if (lean_is_scalar(x_156)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_156;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_155);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_6);
x_166 = lean_ctor_get(x_149, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_149, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_168 = x_149;
} else {
 lean_dec_ref(x_149);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_3);
lean_dec(x_2);
x_170 = !lean_is_exclusive(x_1);
if (x_170 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_1, 1);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_5);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_5, 0);
lean_dec(x_173);
x_174 = lean_ctor_get(x_6, 1);
lean_inc(x_174);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_174);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_1);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_4);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_ctor_get(x_5, 1);
lean_inc(x_177);
lean_dec(x_5);
x_178 = lean_ctor_get(x_6, 1);
lean_inc(x_178);
lean_dec(x_6);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_1, 1, x_179);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_1);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_4);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_182 = lean_ctor_get(x_1, 0);
lean_inc(x_182);
lean_dec(x_1);
x_183 = lean_ctor_get(x_5, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_184 = x_5;
} else {
 lean_dec_ref(x_5);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_6, 1);
lean_inc(x_185);
lean_dec(x_6);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_4);
return x_189;
}
}
}
}
}
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Array_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = l_Array_empty___closed__1;
x_10 = lean_array_push(x_9, x_6);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_7, x_7, x_11, x_9);
lean_dec(x_7);
x_13 = l_Lean_nullKind___closed__2;
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_array_push(x_10, x_14);
x_16 = l_Lean_mkAppStx___closed__8;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_4);
return x_21;
}
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppImplicit___lambda__1), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppExplicit___closed__1;
x_2 = l_Lean_Delaborator_delabAppImplicit___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppImplicit___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppImplicit___closed__2;
x_2 = l_Lean_Delaborator_delabAppImplicit___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Delaborator_withAppFnArgs___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppImplicit___lambda__3___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppImplicit___closed__4;
x_2 = l_Lean_Delaborator_delabAppImplicit___closed__5;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabAppImplicit___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPExplicit___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabAppImplicit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabAppImplicit___closed__7;
x_5 = l_Lean_Delaborator_delabAppImplicit___closed__6;
x_6 = l_Lean_Delaborator_whenNotPPOption(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Delaborator_delabAppImplicit___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_delabAppImplicit___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabAppImplicit), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabAppImplicit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__9;
x_4 = l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Delaborator_hasIdent___main(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Lean_Delaborator_hasIdent___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1(x_1, x_3, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
case 3:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_name_eq(x_1, x_7);
return x_8;
}
default: 
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_hasIdent___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_Delaborator_hasIdent___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Delaborator_hasIdent___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_Delaborator_hasIdent(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Delaborator_hasIdent___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_hasIdent___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Delaborator_hasIdent(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPBinderTypes___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Delaborator_getPPOption___boxed), 4, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Delaborator_1__shouldGroupWithNext(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1;
lean_inc(x_1);
x_9 = l_Lean_Delaborator_getPPOption(x_8, x_1, x_2, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
switch (lean_obj_tag(x_7)) {
case 6:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 6)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_mkThunk___closed__1;
x_17 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2;
x_18 = l_Lean_Delaborator_withBindingBody___rarg(x_16, x_17, x_1, x_2, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_43; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_27 = x_18;
} else {
 lean_dec_ref(x_18);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_30 = l_Lean_Expr_binderInfo(x_7);
x_31 = l_Lean_Expr_binderInfo(x_11);
x_43 = l_Lean_BinderInfo_beq(x_30, x_31);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_7);
x_44 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_26);
lean_ctor_set(x_9, 0, x_44);
return x_9;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = l_Lean_Expr_bindingDomain_x21(x_7);
lean_dec(x_7);
x_46 = l_Lean_Expr_bindingDomain_x21(x_11);
lean_dec(x_11);
x_47 = lean_expr_eqv(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
x_48 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_26);
lean_ctor_set(x_9, 0, x_48);
return x_9;
}
else
{
uint8_t x_49; uint8_t x_50; 
x_49 = 3;
x_50 = l_Lean_BinderInfo_beq(x_31, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_free_object(x_9);
x_51 = lean_unbox(x_15);
lean_dec(x_15);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = lean_unbox(x_28);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = 1;
x_32 = x_53;
goto block_42;
}
else
{
uint8_t x_54; 
x_54 = 0;
x_32 = x_54;
goto block_42;
}
}
else
{
uint8_t x_55; 
x_55 = lean_unbox(x_28);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_32 = x_56;
goto block_42;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_32 = x_57;
goto block_42;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_15);
x_58 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_26);
lean_ctor_set(x_9, 0, x_58);
return x_9;
}
}
}
block_42:
{
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
if (lean_is_scalar(x_27)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_27;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
else
{
uint8_t x_35; uint8_t x_36; 
x_35 = 0;
x_36 = l_Lean_BinderInfo_beq(x_31, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_28);
x_37 = lean_box(x_32);
if (lean_is_scalar(x_29)) {
 x_38 = lean_alloc_ctor(1, 1, 0);
} else {
 x_38 = x_29;
}
lean_ctor_set(x_38, 0, x_37);
if (lean_is_scalar(x_27)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_27;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_26);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
if (lean_is_scalar(x_29)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_29;
}
lean_ctor_set(x_40, 0, x_28);
if (lean_is_scalar(x_27)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_27;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_15);
lean_free_object(x_9);
lean_dec(x_11);
lean_dec(x_7);
x_59 = !lean_is_exclusive(x_18);
if (x_59 == 0)
{
return x_18;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_18, 0);
x_61 = lean_ctor_get(x_18, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_18);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_9, 1);
lean_inc(x_63);
lean_dec(x_9);
x_64 = lean_ctor_get(x_10, 0);
lean_inc(x_64);
lean_dec(x_10);
x_65 = l_Lean_mkThunk___closed__1;
x_66 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2;
x_67 = l_Lean_Delaborator_withBindingBody___rarg(x_65, x_66, x_1, x_2, x_63);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_7);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_90; 
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_74 = x_67;
} else {
 lean_dec_ref(x_67);
 x_74 = lean_box(0);
}
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_76 = x_68;
} else {
 lean_dec_ref(x_68);
 x_76 = lean_box(0);
}
x_77 = l_Lean_Expr_binderInfo(x_7);
x_78 = l_Lean_Expr_binderInfo(x_11);
x_90 = l_Lean_BinderInfo_beq(x_77, x_78);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_7);
x_91 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_73);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_93 = l_Lean_Expr_bindingDomain_x21(x_7);
lean_dec(x_7);
x_94 = l_Lean_Expr_bindingDomain_x21(x_11);
lean_dec(x_11);
x_95 = lean_expr_eqv(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_64);
x_96 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_73);
return x_97;
}
else
{
uint8_t x_98; uint8_t x_99; 
x_98 = 3;
x_99 = l_Lean_BinderInfo_beq(x_78, x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_unbox(x_64);
lean_dec(x_64);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = lean_unbox(x_75);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = 1;
x_79 = x_102;
goto block_89;
}
else
{
uint8_t x_103; 
x_103 = 0;
x_79 = x_103;
goto block_89;
}
}
else
{
uint8_t x_104; 
x_104 = lean_unbox(x_75);
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = 0;
x_79 = x_105;
goto block_89;
}
else
{
uint8_t x_106; 
x_106 = 1;
x_79 = x_106;
goto block_89;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_64);
x_107 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_73);
return x_108;
}
}
}
block_89:
{
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_75);
x_80 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
if (lean_is_scalar(x_74)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_74;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
else
{
uint8_t x_82; uint8_t x_83; 
x_82 = 0;
x_83 = l_Lean_BinderInfo_beq(x_78, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_75);
x_84 = lean_box(x_79);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_76;
}
lean_ctor_set(x_85, 0, x_84);
if (lean_is_scalar(x_74)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_74;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_73);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
if (lean_is_scalar(x_76)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_76;
}
lean_ctor_set(x_87, 0, x_75);
if (lean_is_scalar(x_74)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_74;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_73);
return x_88;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_7);
x_109 = lean_ctor_get(x_67, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_67, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_111 = x_67;
} else {
 lean_dec_ref(x_67);
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
}
else
{
uint8_t x_113; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_9);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_9, 0);
lean_dec(x_114);
x_115 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 0, x_115);
return x_9;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_dec(x_9);
x_117 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
case 7:
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_7, 2);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 7)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_9);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_9, 1);
x_122 = lean_ctor_get(x_9, 0);
lean_dec(x_122);
x_123 = lean_ctor_get(x_10, 0);
lean_inc(x_123);
lean_dec(x_10);
x_124 = l_Lean_mkThunk___closed__1;
x_125 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2;
x_126 = l_Lean_Delaborator_withBindingBody___rarg(x_124, x_125, x_1, x_2, x_121);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
lean_dec(x_123);
lean_free_object(x_9);
lean_dec(x_119);
lean_dec(x_7);
x_128 = !lean_is_exclusive(x_126);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_126, 0);
lean_dec(x_129);
x_130 = lean_box(0);
lean_ctor_set(x_126, 0, x_130);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_151; 
x_134 = lean_ctor_get(x_126, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_135 = x_126;
} else {
 lean_dec_ref(x_126);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_127, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
x_138 = l_Lean_Expr_binderInfo(x_7);
x_139 = l_Lean_Expr_binderInfo(x_119);
x_151 = l_Lean_BinderInfo_beq(x_138, x_139);
if (x_151 == 0)
{
lean_object* x_152; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_123);
lean_dec(x_119);
lean_dec(x_7);
x_152 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_134);
lean_ctor_set(x_9, 0, x_152);
return x_9;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_153 = l_Lean_Expr_bindingDomain_x21(x_7);
lean_dec(x_7);
x_154 = l_Lean_Expr_bindingDomain_x21(x_119);
lean_dec(x_119);
x_155 = lean_expr_eqv(x_153, x_154);
lean_dec(x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_123);
x_156 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_134);
lean_ctor_set(x_9, 0, x_156);
return x_9;
}
else
{
uint8_t x_157; uint8_t x_158; 
x_157 = 3;
x_158 = l_Lean_BinderInfo_beq(x_139, x_157);
if (x_158 == 0)
{
uint8_t x_159; 
lean_free_object(x_9);
x_159 = lean_unbox(x_123);
lean_dec(x_123);
if (x_159 == 0)
{
uint8_t x_160; 
x_160 = lean_unbox(x_136);
if (x_160 == 0)
{
uint8_t x_161; 
x_161 = 1;
x_140 = x_161;
goto block_150;
}
else
{
uint8_t x_162; 
x_162 = 0;
x_140 = x_162;
goto block_150;
}
}
else
{
uint8_t x_163; 
x_163 = lean_unbox(x_136);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = 0;
x_140 = x_164;
goto block_150;
}
else
{
uint8_t x_165; 
x_165 = 1;
x_140 = x_165;
goto block_150;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_123);
x_166 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 1, x_134);
lean_ctor_set(x_9, 0, x_166);
return x_9;
}
}
}
block_150:
{
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_137);
lean_dec(x_136);
x_141 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
if (lean_is_scalar(x_135)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_135;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_134);
return x_142;
}
else
{
uint8_t x_143; uint8_t x_144; 
x_143 = 0;
x_144 = l_Lean_BinderInfo_beq(x_139, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_136);
x_145 = lean_box(x_140);
if (lean_is_scalar(x_137)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_137;
}
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_135)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_135;
}
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_134);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
if (lean_is_scalar(x_137)) {
 x_148 = lean_alloc_ctor(1, 1, 0);
} else {
 x_148 = x_137;
}
lean_ctor_set(x_148, 0, x_136);
if (lean_is_scalar(x_135)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_135;
}
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_134);
return x_149;
}
}
}
}
}
else
{
uint8_t x_167; 
lean_dec(x_123);
lean_free_object(x_9);
lean_dec(x_119);
lean_dec(x_7);
x_167 = !lean_is_exclusive(x_126);
if (x_167 == 0)
{
return x_126;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_126, 0);
x_169 = lean_ctor_get(x_126, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_126);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_9, 1);
lean_inc(x_171);
lean_dec(x_9);
x_172 = lean_ctor_get(x_10, 0);
lean_inc(x_172);
lean_dec(x_10);
x_173 = l_Lean_mkThunk___closed__1;
x_174 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2;
x_175 = l_Lean_Delaborator_withBindingBody___rarg(x_173, x_174, x_1, x_2, x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_172);
lean_dec(x_119);
lean_dec(x_7);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_198; 
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_182 = x_175;
} else {
 lean_dec_ref(x_175);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_176, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
x_185 = l_Lean_Expr_binderInfo(x_7);
x_186 = l_Lean_Expr_binderInfo(x_119);
x_198 = l_Lean_BinderInfo_beq(x_185, x_186);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_172);
lean_dec(x_119);
lean_dec(x_7);
x_199 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_181);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_201 = l_Lean_Expr_bindingDomain_x21(x_7);
lean_dec(x_7);
x_202 = l_Lean_Expr_bindingDomain_x21(x_119);
lean_dec(x_119);
x_203 = lean_expr_eqv(x_201, x_202);
lean_dec(x_202);
lean_dec(x_201);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_172);
x_204 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_181);
return x_205;
}
else
{
uint8_t x_206; uint8_t x_207; 
x_206 = 3;
x_207 = l_Lean_BinderInfo_beq(x_186, x_206);
if (x_207 == 0)
{
uint8_t x_208; 
x_208 = lean_unbox(x_172);
lean_dec(x_172);
if (x_208 == 0)
{
uint8_t x_209; 
x_209 = lean_unbox(x_183);
if (x_209 == 0)
{
uint8_t x_210; 
x_210 = 1;
x_187 = x_210;
goto block_197;
}
else
{
uint8_t x_211; 
x_211 = 0;
x_187 = x_211;
goto block_197;
}
}
else
{
uint8_t x_212; 
x_212 = lean_unbox(x_183);
if (x_212 == 0)
{
uint8_t x_213; 
x_213 = 0;
x_187 = x_213;
goto block_197;
}
else
{
uint8_t x_214; 
x_214 = 1;
x_187 = x_214;
goto block_197;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_172);
x_215 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_181);
return x_216;
}
}
}
block_197:
{
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_184);
lean_dec(x_183);
x_188 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
if (lean_is_scalar(x_182)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_182;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_181);
return x_189;
}
else
{
uint8_t x_190; uint8_t x_191; 
x_190 = 0;
x_191 = l_Lean_BinderInfo_beq(x_186, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_183);
x_192 = lean_box(x_187);
if (lean_is_scalar(x_184)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_184;
}
lean_ctor_set(x_193, 0, x_192);
if (lean_is_scalar(x_182)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_182;
}
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_181);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
if (lean_is_scalar(x_184)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_184;
}
lean_ctor_set(x_195, 0, x_183);
if (lean_is_scalar(x_182)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_182;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_181);
return x_196;
}
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_172);
lean_dec(x_119);
lean_dec(x_7);
x_217 = lean_ctor_get(x_175, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_175, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_219 = x_175;
} else {
 lean_dec_ref(x_175);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_217);
lean_ctor_set(x_220, 1, x_218);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_119);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_9);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_9, 0);
lean_dec(x_222);
x_223 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 0, x_223);
return x_9;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_9, 1);
lean_inc(x_224);
lean_dec(x_9);
x_225 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
}
default: 
{
uint8_t x_227; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_227 = !lean_is_exclusive(x_9);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_9, 0);
lean_dec(x_228);
x_229 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
lean_ctor_set(x_9, 0, x_229);
return x_9;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_9, 1);
lean_inc(x_230);
lean_dec(x_9);
x_231 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3;
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
}
}
lean_object* _init_l___private_Lean_Delaborator_2__delabBinders___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delab), 3, 0);
return x_1;
}
}
lean_object* l___private_Lean_Delaborator_2__delabBinders___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = l_Lean_Delaborator_getExpr(x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_bindingName_x21(x_10);
lean_dec(x_10);
x_12 = lean_local_ctx_get_unused_name(x_6, x_11);
lean_inc(x_12);
x_13 = lean_mk_syntax_ident(x_12);
lean_inc(x_3);
x_14 = l_Lean_Delaborator_annotateCurPos(x_13, x_3, x_4, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_push(x_2, x_17);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l___private_Lean_Delaborator_1__shouldGroupWithNext(x_3, x_4, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_31 = l_Lean_Delaborator_withBindingBody___rarg(x_12, x_30, x_3, x_4, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_apply_5(x_1, x_18, x_40, x_3, x_4, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_31);
if (x_42 == 0)
{
return x_31;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_31, 0);
x_44 = lean_ctor_get(x_31, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_31);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_alloc_closure((void*)(l___private_Lean_Delaborator_2__delabBinders___main), 5, 2);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_18);
x_48 = l_Lean_Delaborator_withBindingBody___rarg(x_12, x_47, x_3, x_4, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l___private_Lean_Delaborator_2__delabBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Delaborator_2__delabBinders___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
x_10 = l_Lean_Delaborator_hasIdent___main(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* _init_l_Lean_Delaborator_delabLam___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabLam___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabLam___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_addParenHeuristic___closed__1;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabLam___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Delaborator_delabLam___lambda__1___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabLam___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Delaborator_getExpr(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Delaborator_withBindingDomain___rarg(x_10, x_3, x_4, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1;
lean_inc(x_3);
x_22 = l_Lean_Delaborator_getPPOption(x_21, x_3, x_4, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_477; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = l_Lean_Delaborator_delabAppImplicit___closed__7;
lean_inc(x_3);
x_29 = l_Lean_Delaborator_getPPOption(x_28, x_3, x_4, x_25);
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
x_477 = !lean_is_exclusive(x_30);
if (x_477 == 0)
{
lean_object* x_478; uint8_t x_479; 
x_478 = lean_ctor_get(x_30, 0);
x_479 = lean_unbox(x_478);
lean_dec(x_478);
if (x_479 == 0)
{
uint8_t x_480; uint8_t x_481; uint8_t x_482; 
x_480 = l_Lean_Expr_binderInfo(x_9);
x_481 = 0;
x_482 = l_Lean_BinderInfo_beq(x_480, x_481);
if (x_482 == 0)
{
uint8_t x_483; 
lean_inc(x_2);
x_483 = l_Lean_Elab_Term_blockImplicitLambda(x_2);
if (x_483 == 0)
{
lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_484 = lean_array_get_size(x_1);
x_485 = lean_unsigned_to_nat(0u);
x_486 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(x_1, x_2, x_1, x_484, x_485);
lean_dec(x_484);
if (x_486 == 0)
{
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_487; 
lean_free_object(x_30);
lean_free_object(x_22);
x_487 = lean_box(0);
x_33 = x_487;
goto block_476;
}
}
else
{
lean_object* x_488; 
lean_free_object(x_30);
lean_free_object(x_22);
x_488 = lean_box(0);
x_33 = x_488;
goto block_476;
}
}
else
{
lean_object* x_489; 
lean_free_object(x_30);
lean_free_object(x_22);
x_489 = lean_box(0);
x_33 = x_489;
goto block_476;
}
}
else
{
lean_object* x_490; 
lean_free_object(x_30);
lean_free_object(x_22);
x_490 = lean_box(0);
x_33 = x_490;
goto block_476;
}
}
else
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_ctor_get(x_30, 0);
lean_inc(x_491);
lean_dec(x_30);
x_492 = lean_unbox(x_491);
lean_dec(x_491);
if (x_492 == 0)
{
uint8_t x_493; uint8_t x_494; uint8_t x_495; 
x_493 = l_Lean_Expr_binderInfo(x_9);
x_494 = 0;
x_495 = l_Lean_BinderInfo_beq(x_493, x_494);
if (x_495 == 0)
{
uint8_t x_496; 
lean_inc(x_2);
x_496 = l_Lean_Elab_Term_blockImplicitLambda(x_2);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_497 = lean_array_get_size(x_1);
x_498 = lean_unsigned_to_nat(0u);
x_499 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(x_1, x_2, x_1, x_497, x_498);
lean_dec(x_497);
if (x_499 == 0)
{
lean_object* x_500; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_2);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_500);
return x_22;
}
else
{
lean_object* x_501; 
lean_free_object(x_22);
x_501 = lean_box(0);
x_33 = x_501;
goto block_476;
}
}
else
{
lean_object* x_502; 
lean_free_object(x_22);
x_502 = lean_box(0);
x_33 = x_502;
goto block_476;
}
}
else
{
lean_object* x_503; 
lean_free_object(x_22);
x_503 = lean_box(0);
x_33 = x_503;
goto block_476;
}
}
else
{
lean_object* x_504; 
lean_free_object(x_22);
x_504 = lean_box(0);
x_33 = x_504;
goto block_476;
}
}
block_476:
{
uint8_t x_34; 
lean_dec(x_33);
x_34 = l_Lean_Expr_binderInfo(x_9);
lean_dec(x_9);
switch (x_34) {
case 0:
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_unbox(x_26);
lean_dec(x_26);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_72; uint8_t x_73; 
lean_dec(x_20);
x_36 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
lean_dec(x_1);
x_72 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_73 = l_Lean_Syntax_isOfKind(x_2, x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = 0;
x_37 = x_74;
goto block_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = l_Lean_Syntax_getArgs(x_2);
x_76 = lean_array_get_size(x_75);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(4u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
x_37 = x_78;
goto block_71;
}
block_71:
{
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = l_Array_empty___closed__1;
x_39 = lean_array_push(x_38, x_36);
x_40 = l_Lean_nullKind___closed__2;
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_43 = lean_array_push(x_42, x_41);
x_44 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_45 = lean_array_push(x_43, x_44);
x_46 = lean_array_push(x_45, x_2);
x_47 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_27;
}
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_32)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_32;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_31);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_unsigned_to_nat(1u);
x_52 = l_Lean_Syntax_getArg(x_2, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = l_Lean_Syntax_getArg(x_2, x_53);
lean_dec(x_2);
x_55 = l_Lean_Syntax_getArgs(x_52);
lean_dec(x_52);
x_56 = l_Array_empty___closed__1;
x_57 = lean_array_push(x_56, x_36);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_55, x_55, x_58, x_57);
lean_dec(x_55);
x_60 = l_Lean_nullKind___closed__2;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_63 = lean_array_push(x_62, x_61);
x_64 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_65 = lean_array_push(x_63, x_64);
x_66 = lean_array_push(x_65, x_54);
x_67 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
if (lean_is_scalar(x_27)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_27;
}
lean_ctor_set(x_69, 0, x_68);
if (lean_is_scalar(x_32)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_32;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_31);
return x_70;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_array_get_size(x_1);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_lt(x_80, x_79);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_131; uint8_t x_132; 
x_82 = l_Lean_Syntax_inhabited;
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_array_get(x_82, x_1, x_83);
lean_dec(x_1);
x_85 = l_Array_empty___closed__1;
x_86 = lean_array_push(x_85, x_84);
x_87 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_88 = lean_array_push(x_87, x_20);
x_89 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = lean_array_push(x_85, x_90);
x_92 = l_Lean_nullKind___closed__2;
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_array_push(x_86, x_93);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_97 = lean_array_push(x_96, x_95);
x_98 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_99 = lean_array_push(x_97, x_98);
x_100 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
x_131 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_132 = l_Lean_Syntax_isOfKind(x_2, x_131);
if (x_132 == 0)
{
uint8_t x_133; 
x_133 = 0;
x_102 = x_133;
goto block_130;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_134 = l_Lean_Syntax_getArgs(x_2);
x_135 = lean_array_get_size(x_134);
lean_dec(x_134);
x_136 = lean_unsigned_to_nat(4u);
x_137 = lean_nat_dec_eq(x_135, x_136);
lean_dec(x_135);
x_102 = x_137;
goto block_130;
}
block_130:
{
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_array_push(x_85, x_101);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_92);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_106 = lean_array_push(x_105, x_104);
x_107 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_108 = lean_array_push(x_106, x_107);
x_109 = lean_array_push(x_108, x_2);
x_110 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
if (lean_is_scalar(x_27)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_27;
}
lean_ctor_set(x_112, 0, x_111);
if (lean_is_scalar(x_32)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_32;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_31);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_114 = l_Lean_Syntax_getArg(x_2, x_80);
x_115 = lean_unsigned_to_nat(3u);
x_116 = l_Lean_Syntax_getArg(x_2, x_115);
lean_dec(x_2);
x_117 = l_Lean_Syntax_getArgs(x_114);
lean_dec(x_114);
x_118 = lean_array_push(x_85, x_101);
x_119 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_117, x_117, x_83, x_118);
lean_dec(x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_92);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_122 = lean_array_push(x_121, x_120);
x_123 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_124 = lean_array_push(x_122, x_123);
x_125 = lean_array_push(x_124, x_116);
x_126 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_125);
if (lean_is_scalar(x_27)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_27;
}
lean_ctor_set(x_128, 0, x_127);
if (lean_is_scalar(x_32)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_32;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_31);
return x_129;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_194; uint8_t x_195; 
x_138 = l_Lean_Syntax_inhabited;
x_139 = lean_unsigned_to_nat(0u);
x_140 = lean_array_get(x_138, x_1, x_139);
x_141 = l_Array_empty___closed__1;
x_142 = lean_array_push(x_141, x_140);
x_143 = l_Array_eraseIdx___rarg(x_1, x_139);
x_144 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_143, x_143, x_139, x_141);
lean_dec(x_143);
x_145 = l_Lean_nullKind___closed__2;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_array_push(x_142, x_146);
x_148 = l_Lean_mkAppStx___closed__8;
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
x_150 = lean_array_push(x_141, x_149);
x_151 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_152 = lean_array_push(x_151, x_20);
x_153 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_array_push(x_141, x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_145);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_array_push(x_150, x_156);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_145);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_160 = lean_array_push(x_159, x_158);
x_161 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_162 = lean_array_push(x_160, x_161);
x_163 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_194 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_195 = l_Lean_Syntax_isOfKind(x_2, x_194);
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = 0;
x_165 = x_196;
goto block_193;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = l_Lean_Syntax_getArgs(x_2);
x_198 = lean_array_get_size(x_197);
lean_dec(x_197);
x_199 = lean_unsigned_to_nat(4u);
x_200 = lean_nat_dec_eq(x_198, x_199);
lean_dec(x_198);
x_165 = x_200;
goto block_193;
}
block_193:
{
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_166 = lean_array_push(x_141, x_164);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_145);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_169 = lean_array_push(x_168, x_167);
x_170 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_171 = lean_array_push(x_169, x_170);
x_172 = lean_array_push(x_171, x_2);
x_173 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
if (lean_is_scalar(x_27)) {
 x_175 = lean_alloc_ctor(1, 1, 0);
} else {
 x_175 = x_27;
}
lean_ctor_set(x_175, 0, x_174);
if (lean_is_scalar(x_32)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_32;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_31);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_177 = l_Lean_Syntax_getArg(x_2, x_80);
x_178 = lean_unsigned_to_nat(3u);
x_179 = l_Lean_Syntax_getArg(x_2, x_178);
lean_dec(x_2);
x_180 = l_Lean_Syntax_getArgs(x_177);
lean_dec(x_177);
x_181 = lean_array_push(x_141, x_164);
x_182 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_180, x_180, x_139, x_181);
lean_dec(x_180);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_145);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_185 = lean_array_push(x_184, x_183);
x_186 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_187 = lean_array_push(x_185, x_186);
x_188 = lean_array_push(x_187, x_179);
x_189 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
if (lean_is_scalar(x_27)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_27;
}
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_32)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_32;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_31);
return x_192;
}
}
}
}
}
case 1:
{
uint8_t x_201; 
lean_dec(x_4);
lean_dec(x_3);
x_201 = lean_unbox(x_26);
lean_dec(x_26);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_245; uint8_t x_246; 
lean_dec(x_20);
x_202 = lean_unsigned_to_nat(0u);
x_203 = l_Array_empty___closed__1;
x_204 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_202, x_203);
lean_dec(x_1);
x_205 = l_Lean_nullKind___closed__2;
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_204);
x_207 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_208 = lean_array_push(x_207, x_206);
x_209 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_210 = lean_array_push(x_208, x_209);
x_211 = l_Lean_Delaborator_delabConst___closed__3;
x_212 = lean_array_push(x_210, x_211);
x_213 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_212);
x_245 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_246 = l_Lean_Syntax_isOfKind(x_2, x_245);
if (x_246 == 0)
{
uint8_t x_247; 
x_247 = 0;
x_215 = x_247;
goto block_244;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; 
x_248 = l_Lean_Syntax_getArgs(x_2);
x_249 = lean_array_get_size(x_248);
lean_dec(x_248);
x_250 = lean_unsigned_to_nat(4u);
x_251 = lean_nat_dec_eq(x_249, x_250);
lean_dec(x_249);
x_215 = x_251;
goto block_244;
}
block_244:
{
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_216 = lean_array_push(x_203, x_214);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_205);
lean_ctor_set(x_217, 1, x_216);
x_218 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_219 = lean_array_push(x_218, x_217);
x_220 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_221 = lean_array_push(x_219, x_220);
x_222 = lean_array_push(x_221, x_2);
x_223 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
if (lean_is_scalar(x_27)) {
 x_225 = lean_alloc_ctor(1, 1, 0);
} else {
 x_225 = x_27;
}
lean_ctor_set(x_225, 0, x_224);
if (lean_is_scalar(x_32)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_32;
}
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_31);
return x_226;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_227 = lean_unsigned_to_nat(1u);
x_228 = l_Lean_Syntax_getArg(x_2, x_227);
x_229 = lean_unsigned_to_nat(3u);
x_230 = l_Lean_Syntax_getArg(x_2, x_229);
lean_dec(x_2);
x_231 = l_Lean_Syntax_getArgs(x_228);
lean_dec(x_228);
x_232 = lean_array_push(x_203, x_214);
x_233 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_231, x_231, x_202, x_232);
lean_dec(x_231);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_205);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_236 = lean_array_push(x_235, x_234);
x_237 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_238 = lean_array_push(x_236, x_237);
x_239 = lean_array_push(x_238, x_230);
x_240 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
if (lean_is_scalar(x_27)) {
 x_242 = lean_alloc_ctor(1, 1, 0);
} else {
 x_242 = x_27;
}
lean_ctor_set(x_242, 0, x_241);
if (lean_is_scalar(x_32)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_32;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_31);
return x_243;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_297; uint8_t x_298; 
x_252 = lean_unsigned_to_nat(0u);
x_253 = l_Array_empty___closed__1;
x_254 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_252, x_253);
lean_dec(x_1);
x_255 = l_Lean_nullKind___closed__2;
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_258 = lean_array_push(x_257, x_256);
x_259 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_260 = lean_array_push(x_259, x_20);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_255);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_array_push(x_258, x_261);
x_263 = l_Lean_Delaborator_delabConst___closed__3;
x_264 = lean_array_push(x_262, x_263);
x_265 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
x_297 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_298 = l_Lean_Syntax_isOfKind(x_2, x_297);
if (x_298 == 0)
{
uint8_t x_299; 
x_299 = 0;
x_267 = x_299;
goto block_296;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_300 = l_Lean_Syntax_getArgs(x_2);
x_301 = lean_array_get_size(x_300);
lean_dec(x_300);
x_302 = lean_unsigned_to_nat(4u);
x_303 = lean_nat_dec_eq(x_301, x_302);
lean_dec(x_301);
x_267 = x_303;
goto block_296;
}
block_296:
{
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_268 = lean_array_push(x_253, x_266);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_255);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_271 = lean_array_push(x_270, x_269);
x_272 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_273 = lean_array_push(x_271, x_272);
x_274 = lean_array_push(x_273, x_2);
x_275 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
if (lean_is_scalar(x_27)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_27;
}
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_32)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_32;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_31);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_279 = lean_unsigned_to_nat(1u);
x_280 = l_Lean_Syntax_getArg(x_2, x_279);
x_281 = lean_unsigned_to_nat(3u);
x_282 = l_Lean_Syntax_getArg(x_2, x_281);
lean_dec(x_2);
x_283 = l_Lean_Syntax_getArgs(x_280);
lean_dec(x_280);
x_284 = lean_array_push(x_253, x_266);
x_285 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_283, x_283, x_252, x_284);
lean_dec(x_283);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_255);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_288 = lean_array_push(x_287, x_286);
x_289 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_290 = lean_array_push(x_288, x_289);
x_291 = lean_array_push(x_290, x_282);
x_292 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_293 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_291);
if (lean_is_scalar(x_27)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_27;
}
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_32)) {
 x_295 = lean_alloc_ctor(0, 2, 0);
} else {
 x_295 = x_32;
}
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_31);
return x_295;
}
}
}
}
case 2:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_1);
x_304 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_305 = l_unreachable_x21___rarg(x_304);
x_306 = lean_apply_3(x_305, x_3, x_4, x_31);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
lean_dec(x_2);
x_308 = !lean_is_exclusive(x_306);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_306, 0);
lean_dec(x_309);
x_310 = lean_box(0);
lean_ctor_set(x_306, 0, x_310);
return x_306;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_306, 1);
lean_inc(x_311);
lean_dec(x_306);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_353; uint8_t x_354; 
x_314 = lean_ctor_get(x_306, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 x_315 = x_306;
} else {
 lean_dec_ref(x_306);
 x_315 = lean_box(0);
}
x_316 = lean_ctor_get(x_307, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 x_317 = x_307;
} else {
 lean_dec_ref(x_307);
 x_317 = lean_box(0);
}
x_353 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_354 = l_Lean_Syntax_isOfKind(x_2, x_353);
if (x_354 == 0)
{
uint8_t x_355; 
x_355 = 0;
x_318 = x_355;
goto block_352;
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_356 = l_Lean_Syntax_getArgs(x_2);
x_357 = lean_array_get_size(x_356);
lean_dec(x_356);
x_358 = lean_unsigned_to_nat(4u);
x_359 = lean_nat_dec_eq(x_357, x_358);
lean_dec(x_357);
x_318 = x_359;
goto block_352;
}
block_352:
{
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_319 = l_Array_empty___closed__1;
x_320 = lean_array_push(x_319, x_316);
x_321 = l_Lean_nullKind___closed__2;
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_320);
x_323 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_324 = lean_array_push(x_323, x_322);
x_325 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_326 = lean_array_push(x_324, x_325);
x_327 = lean_array_push(x_326, x_2);
x_328 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_328);
lean_ctor_set(x_329, 1, x_327);
if (lean_is_scalar(x_317)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_317;
}
lean_ctor_set(x_330, 0, x_329);
if (lean_is_scalar(x_315)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_315;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_314);
return x_331;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_332 = lean_unsigned_to_nat(1u);
x_333 = l_Lean_Syntax_getArg(x_2, x_332);
x_334 = lean_unsigned_to_nat(3u);
x_335 = l_Lean_Syntax_getArg(x_2, x_334);
lean_dec(x_2);
x_336 = l_Lean_Syntax_getArgs(x_333);
lean_dec(x_333);
x_337 = l_Array_empty___closed__1;
x_338 = lean_array_push(x_337, x_316);
x_339 = lean_unsigned_to_nat(0u);
x_340 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_336, x_336, x_339, x_338);
lean_dec(x_336);
x_341 = l_Lean_nullKind___closed__2;
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_340);
x_343 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_344 = lean_array_push(x_343, x_342);
x_345 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_346 = lean_array_push(x_344, x_345);
x_347 = lean_array_push(x_346, x_335);
x_348 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
if (lean_is_scalar(x_317)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_317;
}
lean_ctor_set(x_350, 0, x_349);
if (lean_is_scalar(x_315)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_315;
}
lean_ctor_set(x_351, 0, x_350);
lean_ctor_set(x_351, 1, x_314);
return x_351;
}
}
}
}
else
{
uint8_t x_360; 
lean_dec(x_2);
x_360 = !lean_is_exclusive(x_306);
if (x_360 == 0)
{
return x_306;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_306, 0);
x_362 = lean_ctor_get(x_306, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_306);
x_363 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
return x_363;
}
}
}
case 3:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_409; uint8_t x_410; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_364 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
lean_dec(x_1);
x_365 = l_Array_empty___closed__1;
x_366 = lean_array_push(x_365, x_364);
x_367 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_368 = lean_array_push(x_366, x_367);
x_369 = l_Lean_nullKind___closed__2;
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_368);
x_371 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_372 = lean_array_push(x_371, x_370);
x_373 = lean_array_push(x_372, x_20);
x_374 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_375 = lean_array_push(x_373, x_374);
x_376 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
x_409 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_410 = l_Lean_Syntax_isOfKind(x_2, x_409);
if (x_410 == 0)
{
uint8_t x_411; 
x_411 = 0;
x_378 = x_411;
goto block_408;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_412 = l_Lean_Syntax_getArgs(x_2);
x_413 = lean_array_get_size(x_412);
lean_dec(x_412);
x_414 = lean_unsigned_to_nat(4u);
x_415 = lean_nat_dec_eq(x_413, x_414);
lean_dec(x_413);
x_378 = x_415;
goto block_408;
}
block_408:
{
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_379 = lean_array_push(x_365, x_377);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_369);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_382 = lean_array_push(x_381, x_380);
x_383 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_384 = lean_array_push(x_382, x_383);
x_385 = lean_array_push(x_384, x_2);
x_386 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_385);
if (lean_is_scalar(x_27)) {
 x_388 = lean_alloc_ctor(1, 1, 0);
} else {
 x_388 = x_27;
}
lean_ctor_set(x_388, 0, x_387);
if (lean_is_scalar(x_32)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_32;
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_31);
return x_389;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_390 = lean_unsigned_to_nat(1u);
x_391 = l_Lean_Syntax_getArg(x_2, x_390);
x_392 = lean_unsigned_to_nat(3u);
x_393 = l_Lean_Syntax_getArg(x_2, x_392);
lean_dec(x_2);
x_394 = l_Lean_Syntax_getArgs(x_391);
lean_dec(x_391);
x_395 = lean_array_push(x_365, x_377);
x_396 = lean_unsigned_to_nat(0u);
x_397 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_394, x_394, x_396, x_395);
lean_dec(x_394);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_369);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_400 = lean_array_push(x_399, x_398);
x_401 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_402 = lean_array_push(x_400, x_401);
x_403 = lean_array_push(x_402, x_393);
x_404 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_403);
if (lean_is_scalar(x_27)) {
 x_406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_406 = x_27;
}
lean_ctor_set(x_406, 0, x_405);
if (lean_is_scalar(x_32)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_32;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_31);
return x_407;
}
}
}
default: 
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_1);
x_416 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_417 = l_unreachable_x21___rarg(x_416);
x_418 = lean_apply_3(x_417, x_3, x_4, x_31);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 0);
lean_inc(x_419);
if (lean_obj_tag(x_419) == 0)
{
uint8_t x_420; 
lean_dec(x_2);
x_420 = !lean_is_exclusive(x_418);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_418, 0);
lean_dec(x_421);
x_422 = lean_box(0);
lean_ctor_set(x_418, 0, x_422);
return x_418;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
lean_dec(x_418);
x_424 = lean_box(0);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; lean_object* x_465; uint8_t x_466; 
x_426 = lean_ctor_get(x_418, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_427 = x_418;
} else {
 lean_dec_ref(x_418);
 x_427 = lean_box(0);
}
x_428 = lean_ctor_get(x_419, 0);
lean_inc(x_428);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 x_429 = x_419;
} else {
 lean_dec_ref(x_419);
 x_429 = lean_box(0);
}
x_465 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_466 = l_Lean_Syntax_isOfKind(x_2, x_465);
if (x_466 == 0)
{
uint8_t x_467; 
x_467 = 0;
x_430 = x_467;
goto block_464;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_468 = l_Lean_Syntax_getArgs(x_2);
x_469 = lean_array_get_size(x_468);
lean_dec(x_468);
x_470 = lean_unsigned_to_nat(4u);
x_471 = lean_nat_dec_eq(x_469, x_470);
lean_dec(x_469);
x_430 = x_471;
goto block_464;
}
block_464:
{
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_431 = l_Array_empty___closed__1;
x_432 = lean_array_push(x_431, x_428);
x_433 = l_Lean_nullKind___closed__2;
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
x_435 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_436 = lean_array_push(x_435, x_434);
x_437 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_438 = lean_array_push(x_436, x_437);
x_439 = lean_array_push(x_438, x_2);
x_440 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_439);
if (lean_is_scalar(x_429)) {
 x_442 = lean_alloc_ctor(1, 1, 0);
} else {
 x_442 = x_429;
}
lean_ctor_set(x_442, 0, x_441);
if (lean_is_scalar(x_427)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_427;
}
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_426);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_444 = lean_unsigned_to_nat(1u);
x_445 = l_Lean_Syntax_getArg(x_2, x_444);
x_446 = lean_unsigned_to_nat(3u);
x_447 = l_Lean_Syntax_getArg(x_2, x_446);
lean_dec(x_2);
x_448 = l_Lean_Syntax_getArgs(x_445);
lean_dec(x_445);
x_449 = l_Array_empty___closed__1;
x_450 = lean_array_push(x_449, x_428);
x_451 = lean_unsigned_to_nat(0u);
x_452 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_448, x_448, x_451, x_450);
lean_dec(x_448);
x_453 = l_Lean_nullKind___closed__2;
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_452);
x_455 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_456 = lean_array_push(x_455, x_454);
x_457 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_458 = lean_array_push(x_456, x_457);
x_459 = lean_array_push(x_458, x_447);
x_460 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_459);
if (lean_is_scalar(x_429)) {
 x_462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_462 = x_429;
}
lean_ctor_set(x_462, 0, x_461);
if (lean_is_scalar(x_427)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_427;
}
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_426);
return x_463;
}
}
}
}
else
{
uint8_t x_472; 
lean_dec(x_2);
x_472 = !lean_is_exclusive(x_418);
if (x_472 == 0)
{
return x_418;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_418, 0);
x_474 = lean_ctor_get(x_418, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_418);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_954; lean_object* x_955; uint8_t x_956; 
x_505 = lean_ctor_get(x_22, 0);
x_506 = lean_ctor_get(x_22, 1);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_22);
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_508 = x_505;
} else {
 lean_dec_ref(x_505);
 x_508 = lean_box(0);
}
x_509 = l_Lean_Delaborator_delabAppImplicit___closed__7;
lean_inc(x_3);
x_510 = l_Lean_Delaborator_getPPOption(x_509, x_3, x_4, x_506);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_510)) {
 lean_ctor_release(x_510, 0);
 lean_ctor_release(x_510, 1);
 x_513 = x_510;
} else {
 lean_dec_ref(x_510);
 x_513 = lean_box(0);
}
x_954 = lean_ctor_get(x_511, 0);
lean_inc(x_954);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 x_955 = x_511;
} else {
 lean_dec_ref(x_511);
 x_955 = lean_box(0);
}
x_956 = lean_unbox(x_954);
lean_dec(x_954);
if (x_956 == 0)
{
uint8_t x_957; uint8_t x_958; uint8_t x_959; 
x_957 = l_Lean_Expr_binderInfo(x_9);
x_958 = 0;
x_959 = l_Lean_BinderInfo_beq(x_957, x_958);
if (x_959 == 0)
{
uint8_t x_960; 
lean_inc(x_2);
x_960 = l_Lean_Elab_Term_blockImplicitLambda(x_2);
if (x_960 == 0)
{
lean_object* x_961; lean_object* x_962; uint8_t x_963; 
x_961 = lean_array_get_size(x_1);
x_962 = lean_unsigned_to_nat(0u);
x_963 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(x_1, x_2, x_1, x_961, x_962);
lean_dec(x_961);
if (x_963 == 0)
{
lean_object* x_964; lean_object* x_965; 
lean_dec(x_513);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
if (lean_is_scalar(x_955)) {
 x_964 = lean_alloc_ctor(1, 1, 0);
} else {
 x_964 = x_955;
}
lean_ctor_set(x_964, 0, x_2);
x_965 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_512);
return x_965;
}
else
{
lean_object* x_966; 
lean_dec(x_955);
x_966 = lean_box(0);
x_514 = x_966;
goto block_953;
}
}
else
{
lean_object* x_967; 
lean_dec(x_955);
x_967 = lean_box(0);
x_514 = x_967;
goto block_953;
}
}
else
{
lean_object* x_968; 
lean_dec(x_955);
x_968 = lean_box(0);
x_514 = x_968;
goto block_953;
}
}
else
{
lean_object* x_969; 
lean_dec(x_955);
x_969 = lean_box(0);
x_514 = x_969;
goto block_953;
}
block_953:
{
uint8_t x_515; 
lean_dec(x_514);
x_515 = l_Lean_Expr_binderInfo(x_9);
lean_dec(x_9);
switch (x_515) {
case 0:
{
uint8_t x_516; 
lean_dec(x_4);
lean_dec(x_3);
x_516 = lean_unbox(x_507);
lean_dec(x_507);
if (x_516 == 0)
{
lean_object* x_517; uint8_t x_518; lean_object* x_553; uint8_t x_554; 
lean_dec(x_20);
x_517 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
lean_dec(x_1);
x_553 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_554 = l_Lean_Syntax_isOfKind(x_2, x_553);
if (x_554 == 0)
{
uint8_t x_555; 
x_555 = 0;
x_518 = x_555;
goto block_552;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_556 = l_Lean_Syntax_getArgs(x_2);
x_557 = lean_array_get_size(x_556);
lean_dec(x_556);
x_558 = lean_unsigned_to_nat(4u);
x_559 = lean_nat_dec_eq(x_557, x_558);
lean_dec(x_557);
x_518 = x_559;
goto block_552;
}
block_552:
{
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_519 = l_Array_empty___closed__1;
x_520 = lean_array_push(x_519, x_517);
x_521 = l_Lean_nullKind___closed__2;
x_522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_520);
x_523 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_524 = lean_array_push(x_523, x_522);
x_525 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_526 = lean_array_push(x_524, x_525);
x_527 = lean_array_push(x_526, x_2);
x_528 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_529 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_527);
if (lean_is_scalar(x_508)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_508;
}
lean_ctor_set(x_530, 0, x_529);
if (lean_is_scalar(x_513)) {
 x_531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_531 = x_513;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_512);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_532 = lean_unsigned_to_nat(1u);
x_533 = l_Lean_Syntax_getArg(x_2, x_532);
x_534 = lean_unsigned_to_nat(3u);
x_535 = l_Lean_Syntax_getArg(x_2, x_534);
lean_dec(x_2);
x_536 = l_Lean_Syntax_getArgs(x_533);
lean_dec(x_533);
x_537 = l_Array_empty___closed__1;
x_538 = lean_array_push(x_537, x_517);
x_539 = lean_unsigned_to_nat(0u);
x_540 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_536, x_536, x_539, x_538);
lean_dec(x_536);
x_541 = l_Lean_nullKind___closed__2;
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_540);
x_543 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_544 = lean_array_push(x_543, x_542);
x_545 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_546 = lean_array_push(x_544, x_545);
x_547 = lean_array_push(x_546, x_535);
x_548 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_547);
if (lean_is_scalar(x_508)) {
 x_550 = lean_alloc_ctor(1, 1, 0);
} else {
 x_550 = x_508;
}
lean_ctor_set(x_550, 0, x_549);
if (lean_is_scalar(x_513)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_513;
}
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_512);
return x_551;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_560 = lean_array_get_size(x_1);
x_561 = lean_unsigned_to_nat(1u);
x_562 = lean_nat_dec_lt(x_561, x_560);
lean_dec(x_560);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_612; uint8_t x_613; 
x_563 = l_Lean_Syntax_inhabited;
x_564 = lean_unsigned_to_nat(0u);
x_565 = lean_array_get(x_563, x_1, x_564);
lean_dec(x_1);
x_566 = l_Array_empty___closed__1;
x_567 = lean_array_push(x_566, x_565);
x_568 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_569 = lean_array_push(x_568, x_20);
x_570 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
x_572 = lean_array_push(x_566, x_571);
x_573 = l_Lean_nullKind___closed__2;
x_574 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
x_575 = lean_array_push(x_567, x_574);
x_576 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_576, 0, x_573);
lean_ctor_set(x_576, 1, x_575);
x_577 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_578 = lean_array_push(x_577, x_576);
x_579 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_580 = lean_array_push(x_578, x_579);
x_581 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_580);
x_612 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_613 = l_Lean_Syntax_isOfKind(x_2, x_612);
if (x_613 == 0)
{
uint8_t x_614; 
x_614 = 0;
x_583 = x_614;
goto block_611;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; 
x_615 = l_Lean_Syntax_getArgs(x_2);
x_616 = lean_array_get_size(x_615);
lean_dec(x_615);
x_617 = lean_unsigned_to_nat(4u);
x_618 = lean_nat_dec_eq(x_616, x_617);
lean_dec(x_616);
x_583 = x_618;
goto block_611;
}
block_611:
{
if (x_583 == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_584 = lean_array_push(x_566, x_582);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_573);
lean_ctor_set(x_585, 1, x_584);
x_586 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_587 = lean_array_push(x_586, x_585);
x_588 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_589 = lean_array_push(x_587, x_588);
x_590 = lean_array_push(x_589, x_2);
x_591 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_590);
if (lean_is_scalar(x_508)) {
 x_593 = lean_alloc_ctor(1, 1, 0);
} else {
 x_593 = x_508;
}
lean_ctor_set(x_593, 0, x_592);
if (lean_is_scalar(x_513)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_513;
}
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_512);
return x_594;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_595 = l_Lean_Syntax_getArg(x_2, x_561);
x_596 = lean_unsigned_to_nat(3u);
x_597 = l_Lean_Syntax_getArg(x_2, x_596);
lean_dec(x_2);
x_598 = l_Lean_Syntax_getArgs(x_595);
lean_dec(x_595);
x_599 = lean_array_push(x_566, x_582);
x_600 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_598, x_598, x_564, x_599);
lean_dec(x_598);
x_601 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_601, 0, x_573);
lean_ctor_set(x_601, 1, x_600);
x_602 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_603 = lean_array_push(x_602, x_601);
x_604 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_605 = lean_array_push(x_603, x_604);
x_606 = lean_array_push(x_605, x_597);
x_607 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_606);
if (lean_is_scalar(x_508)) {
 x_609 = lean_alloc_ctor(1, 1, 0);
} else {
 x_609 = x_508;
}
lean_ctor_set(x_609, 0, x_608);
if (lean_is_scalar(x_513)) {
 x_610 = lean_alloc_ctor(0, 2, 0);
} else {
 x_610 = x_513;
}
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_512);
return x_610;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_675; uint8_t x_676; 
x_619 = l_Lean_Syntax_inhabited;
x_620 = lean_unsigned_to_nat(0u);
x_621 = lean_array_get(x_619, x_1, x_620);
x_622 = l_Array_empty___closed__1;
x_623 = lean_array_push(x_622, x_621);
x_624 = l_Array_eraseIdx___rarg(x_1, x_620);
x_625 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_624, x_624, x_620, x_622);
lean_dec(x_624);
x_626 = l_Lean_nullKind___closed__2;
x_627 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_625);
x_628 = lean_array_push(x_623, x_627);
x_629 = l_Lean_mkAppStx___closed__8;
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_628);
x_631 = lean_array_push(x_622, x_630);
x_632 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_633 = lean_array_push(x_632, x_20);
x_634 = l_Lean_Parser_Term_typeAscription___elambda__1___closed__2;
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_633);
x_636 = lean_array_push(x_622, x_635);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_626);
lean_ctor_set(x_637, 1, x_636);
x_638 = lean_array_push(x_631, x_637);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_626);
lean_ctor_set(x_639, 1, x_638);
x_640 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_641 = lean_array_push(x_640, x_639);
x_642 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_643 = lean_array_push(x_641, x_642);
x_644 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__2;
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_643);
x_675 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_676 = l_Lean_Syntax_isOfKind(x_2, x_675);
if (x_676 == 0)
{
uint8_t x_677; 
x_677 = 0;
x_646 = x_677;
goto block_674;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_678 = l_Lean_Syntax_getArgs(x_2);
x_679 = lean_array_get_size(x_678);
lean_dec(x_678);
x_680 = lean_unsigned_to_nat(4u);
x_681 = lean_nat_dec_eq(x_679, x_680);
lean_dec(x_679);
x_646 = x_681;
goto block_674;
}
block_674:
{
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_647 = lean_array_push(x_622, x_645);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_626);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_650 = lean_array_push(x_649, x_648);
x_651 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_652 = lean_array_push(x_650, x_651);
x_653 = lean_array_push(x_652, x_2);
x_654 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_653);
if (lean_is_scalar(x_508)) {
 x_656 = lean_alloc_ctor(1, 1, 0);
} else {
 x_656 = x_508;
}
lean_ctor_set(x_656, 0, x_655);
if (lean_is_scalar(x_513)) {
 x_657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_657 = x_513;
}
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_512);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_658 = l_Lean_Syntax_getArg(x_2, x_561);
x_659 = lean_unsigned_to_nat(3u);
x_660 = l_Lean_Syntax_getArg(x_2, x_659);
lean_dec(x_2);
x_661 = l_Lean_Syntax_getArgs(x_658);
lean_dec(x_658);
x_662 = lean_array_push(x_622, x_645);
x_663 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_661, x_661, x_620, x_662);
lean_dec(x_661);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_626);
lean_ctor_set(x_664, 1, x_663);
x_665 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_666 = lean_array_push(x_665, x_664);
x_667 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_668 = lean_array_push(x_666, x_667);
x_669 = lean_array_push(x_668, x_660);
x_670 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_669);
if (lean_is_scalar(x_508)) {
 x_672 = lean_alloc_ctor(1, 1, 0);
} else {
 x_672 = x_508;
}
lean_ctor_set(x_672, 0, x_671);
if (lean_is_scalar(x_513)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_513;
}
lean_ctor_set(x_673, 0, x_672);
lean_ctor_set(x_673, 1, x_512);
return x_673;
}
}
}
}
}
case 1:
{
uint8_t x_682; 
lean_dec(x_4);
lean_dec(x_3);
x_682 = lean_unbox(x_507);
lean_dec(x_507);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_726; uint8_t x_727; 
lean_dec(x_20);
x_683 = lean_unsigned_to_nat(0u);
x_684 = l_Array_empty___closed__1;
x_685 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_683, x_684);
lean_dec(x_1);
x_686 = l_Lean_nullKind___closed__2;
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
x_688 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_689 = lean_array_push(x_688, x_687);
x_690 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_691 = lean_array_push(x_689, x_690);
x_692 = l_Lean_Delaborator_delabConst___closed__3;
x_693 = lean_array_push(x_691, x_692);
x_694 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_694);
lean_ctor_set(x_695, 1, x_693);
x_726 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_727 = l_Lean_Syntax_isOfKind(x_2, x_726);
if (x_727 == 0)
{
uint8_t x_728; 
x_728 = 0;
x_696 = x_728;
goto block_725;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; 
x_729 = l_Lean_Syntax_getArgs(x_2);
x_730 = lean_array_get_size(x_729);
lean_dec(x_729);
x_731 = lean_unsigned_to_nat(4u);
x_732 = lean_nat_dec_eq(x_730, x_731);
lean_dec(x_730);
x_696 = x_732;
goto block_725;
}
block_725:
{
if (x_696 == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_697 = lean_array_push(x_684, x_695);
x_698 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_698, 0, x_686);
lean_ctor_set(x_698, 1, x_697);
x_699 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_700 = lean_array_push(x_699, x_698);
x_701 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_702 = lean_array_push(x_700, x_701);
x_703 = lean_array_push(x_702, x_2);
x_704 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
if (lean_is_scalar(x_508)) {
 x_706 = lean_alloc_ctor(1, 1, 0);
} else {
 x_706 = x_508;
}
lean_ctor_set(x_706, 0, x_705);
if (lean_is_scalar(x_513)) {
 x_707 = lean_alloc_ctor(0, 2, 0);
} else {
 x_707 = x_513;
}
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_512);
return x_707;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_708 = lean_unsigned_to_nat(1u);
x_709 = l_Lean_Syntax_getArg(x_2, x_708);
x_710 = lean_unsigned_to_nat(3u);
x_711 = l_Lean_Syntax_getArg(x_2, x_710);
lean_dec(x_2);
x_712 = l_Lean_Syntax_getArgs(x_709);
lean_dec(x_709);
x_713 = lean_array_push(x_684, x_695);
x_714 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_712, x_712, x_683, x_713);
lean_dec(x_712);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_686);
lean_ctor_set(x_715, 1, x_714);
x_716 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_717 = lean_array_push(x_716, x_715);
x_718 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_719 = lean_array_push(x_717, x_718);
x_720 = lean_array_push(x_719, x_711);
x_721 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_721);
lean_ctor_set(x_722, 1, x_720);
if (lean_is_scalar(x_508)) {
 x_723 = lean_alloc_ctor(1, 1, 0);
} else {
 x_723 = x_508;
}
lean_ctor_set(x_723, 0, x_722);
if (lean_is_scalar(x_513)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_513;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_512);
return x_724;
}
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; uint8_t x_748; lean_object* x_778; uint8_t x_779; 
x_733 = lean_unsigned_to_nat(0u);
x_734 = l_Array_empty___closed__1;
x_735 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_733, x_734);
lean_dec(x_1);
x_736 = l_Lean_nullKind___closed__2;
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_735);
x_738 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_739 = lean_array_push(x_738, x_737);
x_740 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_741 = lean_array_push(x_740, x_20);
x_742 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_742, 0, x_736);
lean_ctor_set(x_742, 1, x_741);
x_743 = lean_array_push(x_739, x_742);
x_744 = l_Lean_Delaborator_delabConst___closed__3;
x_745 = lean_array_push(x_743, x_744);
x_746 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_747 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_747, 0, x_746);
lean_ctor_set(x_747, 1, x_745);
x_778 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_779 = l_Lean_Syntax_isOfKind(x_2, x_778);
if (x_779 == 0)
{
uint8_t x_780; 
x_780 = 0;
x_748 = x_780;
goto block_777;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; 
x_781 = l_Lean_Syntax_getArgs(x_2);
x_782 = lean_array_get_size(x_781);
lean_dec(x_781);
x_783 = lean_unsigned_to_nat(4u);
x_784 = lean_nat_dec_eq(x_782, x_783);
lean_dec(x_782);
x_748 = x_784;
goto block_777;
}
block_777:
{
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_749 = lean_array_push(x_734, x_747);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_736);
lean_ctor_set(x_750, 1, x_749);
x_751 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_752 = lean_array_push(x_751, x_750);
x_753 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_754 = lean_array_push(x_752, x_753);
x_755 = lean_array_push(x_754, x_2);
x_756 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_757 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_755);
if (lean_is_scalar(x_508)) {
 x_758 = lean_alloc_ctor(1, 1, 0);
} else {
 x_758 = x_508;
}
lean_ctor_set(x_758, 0, x_757);
if (lean_is_scalar(x_513)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_513;
}
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_512);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_760 = lean_unsigned_to_nat(1u);
x_761 = l_Lean_Syntax_getArg(x_2, x_760);
x_762 = lean_unsigned_to_nat(3u);
x_763 = l_Lean_Syntax_getArg(x_2, x_762);
lean_dec(x_2);
x_764 = l_Lean_Syntax_getArgs(x_761);
lean_dec(x_761);
x_765 = lean_array_push(x_734, x_747);
x_766 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_764, x_764, x_733, x_765);
lean_dec(x_764);
x_767 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_767, 0, x_736);
lean_ctor_set(x_767, 1, x_766);
x_768 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_769 = lean_array_push(x_768, x_767);
x_770 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_771 = lean_array_push(x_769, x_770);
x_772 = lean_array_push(x_771, x_763);
x_773 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_774 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_772);
if (lean_is_scalar(x_508)) {
 x_775 = lean_alloc_ctor(1, 1, 0);
} else {
 x_775 = x_508;
}
lean_ctor_set(x_775, 0, x_774);
if (lean_is_scalar(x_513)) {
 x_776 = lean_alloc_ctor(0, 2, 0);
} else {
 x_776 = x_513;
}
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_512);
return x_776;
}
}
}
}
case 2:
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_513);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_20);
lean_dec(x_1);
x_785 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_786 = l_unreachable_x21___rarg(x_785);
x_787 = lean_apply_3(x_786, x_3, x_4, x_512);
if (lean_obj_tag(x_787) == 0)
{
lean_object* x_788; 
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
if (lean_obj_tag(x_788) == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_dec(x_2);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_790 = x_787;
} else {
 lean_dec_ref(x_787);
 x_790 = lean_box(0);
}
x_791 = lean_box(0);
if (lean_is_scalar(x_790)) {
 x_792 = lean_alloc_ctor(0, 2, 0);
} else {
 x_792 = x_790;
}
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_789);
return x_792;
}
else
{
lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; uint8_t x_797; lean_object* x_832; uint8_t x_833; 
x_793 = lean_ctor_get(x_787, 1);
lean_inc(x_793);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_794 = x_787;
} else {
 lean_dec_ref(x_787);
 x_794 = lean_box(0);
}
x_795 = lean_ctor_get(x_788, 0);
lean_inc(x_795);
if (lean_is_exclusive(x_788)) {
 lean_ctor_release(x_788, 0);
 x_796 = x_788;
} else {
 lean_dec_ref(x_788);
 x_796 = lean_box(0);
}
x_832 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_833 = l_Lean_Syntax_isOfKind(x_2, x_832);
if (x_833 == 0)
{
uint8_t x_834; 
x_834 = 0;
x_797 = x_834;
goto block_831;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; uint8_t x_838; 
x_835 = l_Lean_Syntax_getArgs(x_2);
x_836 = lean_array_get_size(x_835);
lean_dec(x_835);
x_837 = lean_unsigned_to_nat(4u);
x_838 = lean_nat_dec_eq(x_836, x_837);
lean_dec(x_836);
x_797 = x_838;
goto block_831;
}
block_831:
{
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_798 = l_Array_empty___closed__1;
x_799 = lean_array_push(x_798, x_795);
x_800 = l_Lean_nullKind___closed__2;
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_799);
x_802 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_803 = lean_array_push(x_802, x_801);
x_804 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_805 = lean_array_push(x_803, x_804);
x_806 = lean_array_push(x_805, x_2);
x_807 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_808, 0, x_807);
lean_ctor_set(x_808, 1, x_806);
if (lean_is_scalar(x_796)) {
 x_809 = lean_alloc_ctor(1, 1, 0);
} else {
 x_809 = x_796;
}
lean_ctor_set(x_809, 0, x_808);
if (lean_is_scalar(x_794)) {
 x_810 = lean_alloc_ctor(0, 2, 0);
} else {
 x_810 = x_794;
}
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_793);
return x_810;
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_811 = lean_unsigned_to_nat(1u);
x_812 = l_Lean_Syntax_getArg(x_2, x_811);
x_813 = lean_unsigned_to_nat(3u);
x_814 = l_Lean_Syntax_getArg(x_2, x_813);
lean_dec(x_2);
x_815 = l_Lean_Syntax_getArgs(x_812);
lean_dec(x_812);
x_816 = l_Array_empty___closed__1;
x_817 = lean_array_push(x_816, x_795);
x_818 = lean_unsigned_to_nat(0u);
x_819 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_815, x_815, x_818, x_817);
lean_dec(x_815);
x_820 = l_Lean_nullKind___closed__2;
x_821 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_821, 0, x_820);
lean_ctor_set(x_821, 1, x_819);
x_822 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_823 = lean_array_push(x_822, x_821);
x_824 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_825 = lean_array_push(x_823, x_824);
x_826 = lean_array_push(x_825, x_814);
x_827 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_826);
if (lean_is_scalar(x_796)) {
 x_829 = lean_alloc_ctor(1, 1, 0);
} else {
 x_829 = x_796;
}
lean_ctor_set(x_829, 0, x_828);
if (lean_is_scalar(x_794)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_794;
}
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_793);
return x_830;
}
}
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_2);
x_839 = lean_ctor_get(x_787, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_787, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_841 = x_787;
} else {
 lean_dec_ref(x_787);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
case 3:
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_888; uint8_t x_889; 
lean_dec(x_507);
lean_dec(x_4);
lean_dec(x_3);
x_843 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
lean_dec(x_1);
x_844 = l_Array_empty___closed__1;
x_845 = lean_array_push(x_844, x_843);
x_846 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_847 = lean_array_push(x_845, x_846);
x_848 = l_Lean_nullKind___closed__2;
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_848);
lean_ctor_set(x_849, 1, x_847);
x_850 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_851 = lean_array_push(x_850, x_849);
x_852 = lean_array_push(x_851, x_20);
x_853 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_854 = lean_array_push(x_852, x_853);
x_855 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_856 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_854);
x_888 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_889 = l_Lean_Syntax_isOfKind(x_2, x_888);
if (x_889 == 0)
{
uint8_t x_890; 
x_890 = 0;
x_857 = x_890;
goto block_887;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; 
x_891 = l_Lean_Syntax_getArgs(x_2);
x_892 = lean_array_get_size(x_891);
lean_dec(x_891);
x_893 = lean_unsigned_to_nat(4u);
x_894 = lean_nat_dec_eq(x_892, x_893);
lean_dec(x_892);
x_857 = x_894;
goto block_887;
}
block_887:
{
if (x_857 == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_858 = lean_array_push(x_844, x_856);
x_859 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_859, 0, x_848);
lean_ctor_set(x_859, 1, x_858);
x_860 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_861 = lean_array_push(x_860, x_859);
x_862 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_863 = lean_array_push(x_861, x_862);
x_864 = lean_array_push(x_863, x_2);
x_865 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_864);
if (lean_is_scalar(x_508)) {
 x_867 = lean_alloc_ctor(1, 1, 0);
} else {
 x_867 = x_508;
}
lean_ctor_set(x_867, 0, x_866);
if (lean_is_scalar(x_513)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_513;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_512);
return x_868;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_869 = lean_unsigned_to_nat(1u);
x_870 = l_Lean_Syntax_getArg(x_2, x_869);
x_871 = lean_unsigned_to_nat(3u);
x_872 = l_Lean_Syntax_getArg(x_2, x_871);
lean_dec(x_2);
x_873 = l_Lean_Syntax_getArgs(x_870);
lean_dec(x_870);
x_874 = lean_array_push(x_844, x_856);
x_875 = lean_unsigned_to_nat(0u);
x_876 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_873, x_873, x_875, x_874);
lean_dec(x_873);
x_877 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_877, 0, x_848);
lean_ctor_set(x_877, 1, x_876);
x_878 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_879 = lean_array_push(x_878, x_877);
x_880 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_881 = lean_array_push(x_879, x_880);
x_882 = lean_array_push(x_881, x_872);
x_883 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_884 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_884, 0, x_883);
lean_ctor_set(x_884, 1, x_882);
if (lean_is_scalar(x_508)) {
 x_885 = lean_alloc_ctor(1, 1, 0);
} else {
 x_885 = x_508;
}
lean_ctor_set(x_885, 0, x_884);
if (lean_is_scalar(x_513)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_513;
}
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_512);
return x_886;
}
}
}
default: 
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; 
lean_dec(x_513);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_20);
lean_dec(x_1);
x_895 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_896 = l_unreachable_x21___rarg(x_895);
x_897 = lean_apply_3(x_896, x_3, x_4, x_512);
if (lean_obj_tag(x_897) == 0)
{
lean_object* x_898; 
x_898 = lean_ctor_get(x_897, 0);
lean_inc(x_898);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
lean_dec(x_2);
x_899 = lean_ctor_get(x_897, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_900 = x_897;
} else {
 lean_dec_ref(x_897);
 x_900 = lean_box(0);
}
x_901 = lean_box(0);
if (lean_is_scalar(x_900)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_900;
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_899);
return x_902;
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; lean_object* x_942; uint8_t x_943; 
x_903 = lean_ctor_get(x_897, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_904 = x_897;
} else {
 lean_dec_ref(x_897);
 x_904 = lean_box(0);
}
x_905 = lean_ctor_get(x_898, 0);
lean_inc(x_905);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 x_906 = x_898;
} else {
 lean_dec_ref(x_898);
 x_906 = lean_box(0);
}
x_942 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_inc(x_2);
x_943 = l_Lean_Syntax_isOfKind(x_2, x_942);
if (x_943 == 0)
{
uint8_t x_944; 
x_944 = 0;
x_907 = x_944;
goto block_941;
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_948; 
x_945 = l_Lean_Syntax_getArgs(x_2);
x_946 = lean_array_get_size(x_945);
lean_dec(x_945);
x_947 = lean_unsigned_to_nat(4u);
x_948 = lean_nat_dec_eq(x_946, x_947);
lean_dec(x_946);
x_907 = x_948;
goto block_941;
}
block_941:
{
if (x_907 == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
x_908 = l_Array_empty___closed__1;
x_909 = lean_array_push(x_908, x_905);
x_910 = l_Lean_nullKind___closed__2;
x_911 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_909);
x_912 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_913 = lean_array_push(x_912, x_911);
x_914 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_915 = lean_array_push(x_913, x_914);
x_916 = lean_array_push(x_915, x_2);
x_917 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_916);
if (lean_is_scalar(x_906)) {
 x_919 = lean_alloc_ctor(1, 1, 0);
} else {
 x_919 = x_906;
}
lean_ctor_set(x_919, 0, x_918);
if (lean_is_scalar(x_904)) {
 x_920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_920 = x_904;
}
lean_ctor_set(x_920, 0, x_919);
lean_ctor_set(x_920, 1, x_903);
return x_920;
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_921 = lean_unsigned_to_nat(1u);
x_922 = l_Lean_Syntax_getArg(x_2, x_921);
x_923 = lean_unsigned_to_nat(3u);
x_924 = l_Lean_Syntax_getArg(x_2, x_923);
lean_dec(x_2);
x_925 = l_Lean_Syntax_getArgs(x_922);
lean_dec(x_922);
x_926 = l_Array_empty___closed__1;
x_927 = lean_array_push(x_926, x_905);
x_928 = lean_unsigned_to_nat(0u);
x_929 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_925, x_925, x_928, x_927);
lean_dec(x_925);
x_930 = l_Lean_nullKind___closed__2;
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_929);
x_932 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_933 = lean_array_push(x_932, x_931);
x_934 = l_Lean_Elab_Term_expandCDot_x3f___closed__4;
x_935 = lean_array_push(x_933, x_934);
x_936 = lean_array_push(x_935, x_924);
x_937 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_938 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_936);
if (lean_is_scalar(x_906)) {
 x_939 = lean_alloc_ctor(1, 1, 0);
} else {
 x_939 = x_906;
}
lean_ctor_set(x_939, 0, x_938);
if (lean_is_scalar(x_904)) {
 x_940 = lean_alloc_ctor(0, 2, 0);
} else {
 x_940 = x_904;
}
lean_ctor_set(x_940, 0, x_939);
lean_ctor_set(x_940, 1, x_903);
return x_940;
}
}
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_2);
x_949 = lean_ctor_get(x_897, 0);
lean_inc(x_949);
x_950 = lean_ctor_get(x_897, 1);
lean_inc(x_950);
if (lean_is_exclusive(x_897)) {
 lean_ctor_release(x_897, 0);
 lean_ctor_release(x_897, 1);
 x_951 = x_897;
} else {
 lean_dec_ref(x_897);
 x_951 = lean_box(0);
}
if (lean_is_scalar(x_951)) {
 x_952 = lean_alloc_ctor(1, 2, 0);
} else {
 x_952 = x_951;
}
lean_ctor_set(x_952, 0, x_949);
lean_ctor_set(x_952, 1, x_950);
return x_952;
}
}
}
}
}
}
}
else
{
uint8_t x_970; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_970 = !lean_is_exclusive(x_11);
if (x_970 == 0)
{
return x_11;
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_971 = lean_ctor_get(x_11, 0);
x_972 = lean_ctor_get(x_11, 1);
lean_inc(x_972);
lean_inc(x_971);
lean_dec(x_11);
x_973 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set(x_973, 1, x_972);
return x_973;
}
}
}
}
lean_object* _init_l_Lean_Delaborator_delabLam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabLam___lambda__1), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabLam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabLam___closed__1;
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Lean_Delaborator_2__delabBinders___main(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabLam___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabLam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabLam), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabLam(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__11;
x_4 = l___regBuiltin_Lean_Delaborator_delabLam___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_Syntax_getId(x_8);
lean_dec(x_8);
x_10 = l_Lean_Delaborator_hasIdent___main(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_5, x_11);
lean_dec(x_5);
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_5);
return x_10;
}
}
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Command_openRenamingItem___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_4, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_4, x_12);
lean_dec(x_4);
x_14 = l_Array_empty___closed__1;
lean_inc(x_2);
x_15 = lean_array_push(x_14, x_2);
x_16 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_array_push(x_17, x_6);
x_19 = l_Lean_Parser_Term_arrow___elambda__1___closed__2;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_4 = x_13;
x_5 = lean_box(0);
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
lean_object* l_Lean_Delaborator_delabForall___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_Delaborator_getExpr(x_3, x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Delaborator_withBindingDomain___rarg(x_10, x_3, x_4, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = l_Lean_Expr_binderInfo(x_9);
lean_dec(x_9);
x_25 = lean_box(x_24);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_array_get_size(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(x_1, x_2, x_1, x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_12);
lean_free_object(x_11);
x_29 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(x_1, x_23, x_1, x_26, lean_box(0), x_2, x_3, x_4, x_20);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
x_30 = l_Array_empty___closed__1;
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_27, x_30);
x_32 = l_Lean_nullKind___closed__2;
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_35 = lean_array_push(x_34, x_33);
x_36 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_37 = lean_array_push(x_36, x_23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_array_push(x_35, x_38);
x_40 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_41 = lean_array_push(x_39, x_40);
x_42 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_43 = lean_array_push(x_41, x_42);
x_44 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_push(x_30, x_45);
x_47 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_array_push(x_48, x_2);
x_50 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_12, 0, x_51);
return x_11;
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
lean_dec(x_3);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_empty___closed__1;
x_54 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_52, x_53);
x_55 = l_Lean_nullKind___closed__2;
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_58 = lean_array_push(x_57, x_56);
x_59 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_60 = lean_array_push(x_59, x_23);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_58, x_61);
x_63 = l_Lean_Delaborator_delabConst___closed__3;
x_64 = lean_array_push(x_62, x_63);
x_65 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_53, x_66);
x_68 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_array_push(x_69, x_2);
x_71 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
lean_ctor_set(x_12, 0, x_72);
return x_11;
}
case 3:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_4);
lean_dec(x_3);
x_73 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_74 = l_Array_empty___closed__1;
x_75 = lean_array_push(x_74, x_73);
x_76 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_77 = lean_array_push(x_75, x_76);
x_78 = l_Lean_nullKind___closed__2;
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_81 = lean_array_push(x_80, x_79);
x_82 = lean_array_push(x_81, x_23);
x_83 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_84 = lean_array_push(x_82, x_83);
x_85 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = lean_array_push(x_74, x_86);
x_88 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_89 = lean_array_push(x_87, x_88);
x_90 = lean_array_push(x_89, x_2);
x_91 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
lean_ctor_set(x_12, 0, x_92);
return x_11;
}
default: 
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_25);
lean_free_object(x_12);
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_2);
x_93 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_94 = l_unreachable_x21___rarg(x_93);
x_95 = lean_apply_3(x_94, x_3, x_4, x_20);
return x_95;
}
}
}
else
{
lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_12, 0);
lean_inc(x_96);
lean_dec(x_12);
x_97 = l_Lean_Expr_binderInfo(x_9);
lean_dec(x_9);
x_98 = lean_box(x_97);
switch (lean_obj_tag(x_98)) {
case 0:
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_array_get_size(x_1);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(x_1, x_2, x_1, x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_free_object(x_11);
x_102 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(x_1, x_96, x_1, x_99, lean_box(0), x_2, x_3, x_4, x_20);
lean_dec(x_4);
lean_dec(x_3);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_99);
lean_dec(x_4);
lean_dec(x_3);
x_103 = l_Array_empty___closed__1;
x_104 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_100, x_103);
x_105 = l_Lean_nullKind___closed__2;
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_108 = lean_array_push(x_107, x_106);
x_109 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_110 = lean_array_push(x_109, x_96);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_105);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_array_push(x_108, x_111);
x_113 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_114 = lean_array_push(x_112, x_113);
x_115 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_116 = lean_array_push(x_114, x_115);
x_117 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_103, x_118);
x_120 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_121 = lean_array_push(x_119, x_120);
x_122 = lean_array_push(x_121, x_2);
x_123 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_11, 0, x_125);
return x_11;
}
}
case 1:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_4);
lean_dec(x_3);
x_126 = lean_unsigned_to_nat(0u);
x_127 = l_Array_empty___closed__1;
x_128 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_126, x_127);
x_129 = l_Lean_nullKind___closed__2;
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_128);
x_131 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_132 = lean_array_push(x_131, x_130);
x_133 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_134 = lean_array_push(x_133, x_96);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_array_push(x_132, x_135);
x_137 = l_Lean_Delaborator_delabConst___closed__3;
x_138 = lean_array_push(x_136, x_137);
x_139 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = lean_array_push(x_127, x_140);
x_142 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_143 = lean_array_push(x_141, x_142);
x_144 = lean_array_push(x_143, x_2);
x_145 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_11, 0, x_147);
return x_11;
}
case 3:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_4);
lean_dec(x_3);
x_148 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_149 = l_Array_empty___closed__1;
x_150 = lean_array_push(x_149, x_148);
x_151 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_152 = lean_array_push(x_150, x_151);
x_153 = l_Lean_nullKind___closed__2;
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_156 = lean_array_push(x_155, x_154);
x_157 = lean_array_push(x_156, x_96);
x_158 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_159 = lean_array_push(x_157, x_158);
x_160 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
x_162 = lean_array_push(x_149, x_161);
x_163 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_164 = lean_array_push(x_162, x_163);
x_165 = lean_array_push(x_164, x_2);
x_166 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_11, 0, x_168);
return x_11;
}
default: 
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_98);
lean_dec(x_96);
lean_free_object(x_11);
lean_dec(x_2);
x_169 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_170 = l_unreachable_x21___rarg(x_169);
x_171 = lean_apply_3(x_170, x_3, x_4, x_20);
return x_171;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_11, 1);
lean_inc(x_172);
lean_dec(x_11);
x_173 = lean_ctor_get(x_12, 0);
lean_inc(x_173);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_174 = x_12;
} else {
 lean_dec_ref(x_12);
 x_174 = lean_box(0);
}
x_175 = l_Lean_Expr_binderInfo(x_9);
lean_dec(x_9);
x_176 = lean_box(x_175);
switch (lean_obj_tag(x_176)) {
case 0:
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_array_get_size(x_1);
x_178 = lean_unsigned_to_nat(0u);
x_179 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(x_1, x_2, x_1, x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_174);
x_180 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(x_1, x_173, x_1, x_177, lean_box(0), x_2, x_3, x_4, x_172);
lean_dec(x_4);
lean_dec(x_3);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_177);
lean_dec(x_4);
lean_dec(x_3);
x_181 = l_Array_empty___closed__1;
x_182 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_178, x_181);
x_183 = l_Lean_nullKind___closed__2;
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_182);
x_185 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__4;
x_186 = lean_array_push(x_185, x_184);
x_187 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_188 = lean_array_push(x_187, x_173);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_array_push(x_186, x_189);
x_191 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__5;
x_192 = lean_array_push(x_190, x_191);
x_193 = l_Lean_PrettyPrinter_Parenthesizer_term_parenthesizer___lambda__1___closed__6;
x_194 = lean_array_push(x_192, x_193);
x_195 = l_Lean_Parser_Term_explicitBinder___elambda__1___closed__2;
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_194);
x_197 = lean_array_push(x_181, x_196);
x_198 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_199 = lean_array_push(x_197, x_198);
x_200 = lean_array_push(x_199, x_2);
x_201 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_200);
if (lean_is_scalar(x_174)) {
 x_203 = lean_alloc_ctor(1, 1, 0);
} else {
 x_203 = x_174;
}
lean_ctor_set(x_203, 0, x_202);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_172);
return x_204;
}
}
case 1:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_4);
lean_dec(x_3);
x_205 = lean_unsigned_to_nat(0u);
x_206 = l_Array_empty___closed__1;
x_207 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_205, x_206);
x_208 = l_Lean_nullKind___closed__2;
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
x_210 = l_Lean_Delaborator_delabLam___lambda__1___closed__4;
x_211 = lean_array_push(x_210, x_209);
x_212 = l_Lean_Delaborator_delabLam___lambda__1___closed__2;
x_213 = lean_array_push(x_212, x_173);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_208);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_array_push(x_211, x_214);
x_216 = l_Lean_Delaborator_delabConst___closed__3;
x_217 = lean_array_push(x_215, x_216);
x_218 = l_Lean_Parser_Term_implicitBinder___elambda__1___closed__2;
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_217);
x_220 = lean_array_push(x_206, x_219);
x_221 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_222 = lean_array_push(x_220, x_221);
x_223 = lean_array_push(x_222, x_2);
x_224 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
if (lean_is_scalar(x_174)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_174;
}
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_172);
return x_227;
}
case 3:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_4);
lean_dec(x_3);
x_228 = l_Array_back___at_Lean_Syntax_Traverser_up___spec__2(x_1);
x_229 = l_Array_empty___closed__1;
x_230 = lean_array_push(x_229, x_228);
x_231 = l_Lean_Delaborator_delabLam___lambda__1___closed__1;
x_232 = lean_array_push(x_230, x_231);
x_233 = l_Lean_nullKind___closed__2;
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l_Lean_Elab_Term_expandArrayLit___closed__8;
x_236 = lean_array_push(x_235, x_234);
x_237 = lean_array_push(x_236, x_173);
x_238 = l_Lean_Elab_Term_expandArrayLit___closed__9;
x_239 = lean_array_push(x_237, x_238);
x_240 = l_Lean_Parser_Term_instBinder___elambda__1___closed__2;
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_239);
x_242 = lean_array_push(x_229, x_241);
x_243 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1;
x_244 = lean_array_push(x_242, x_243);
x_245 = lean_array_push(x_244, x_2);
x_246 = l_Lean_Parser_Term_depArrow___elambda__1___closed__2;
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
if (lean_is_scalar(x_174)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_174;
}
lean_ctor_set(x_248, 0, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_172);
return x_249;
}
default: 
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_176);
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_2);
x_250 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_251 = l_unreachable_x21___rarg(x_250);
x_252 = lean_apply_3(x_251, x_3, x_4, x_172);
return x_252;
}
}
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_253 = !lean_is_exclusive(x_11);
if (x_253 == 0)
{
return x_11;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_11, 0);
x_255 = lean_ctor_get(x_11, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_11);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
}
lean_object* _init_l_Lean_Delaborator_delabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabForall___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabForall(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabForall___closed__1;
x_5 = l_Array_empty___closed__1;
x_6 = l___private_Lean_Delaborator_2__delabBinders___main(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Delaborator_delabForall___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Delaborator_delabForall___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Delaborator_delabForall___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabForall), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabForall(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__13;
x_4 = l___regBuiltin_Lean_Delaborator_delabForall___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabLit(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
if (lean_obj_tag(x_7) == 9)
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Nat_repr(x_11);
x_13 = l_Lean_numLitKind;
x_14 = l_Lean_SourceInfo_inhabited___closed__1;
x_15 = l_Lean_mkStxLit(x_13, x_12, x_14);
lean_ctor_set(x_5, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Nat_repr(x_17);
x_19 = l_Lean_numLitKind;
x_20 = l_Lean_SourceInfo_inhabited___closed__1;
x_21 = l_Lean_mkStxLit(x_19, x_18, x_20);
lean_ctor_set(x_5, 0, x_21);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_4, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = l_Lean_SourceInfo_inhabited___closed__1;
x_27 = l_Lean_mkStxStrLit(x_25, x_26);
lean_ctor_set(x_5, 0, x_27);
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_4, 1);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
x_30 = l_Lean_SourceInfo_inhabited___closed__1;
x_31 = l_Lean_mkStxStrLit(x_29, x_30);
lean_ctor_set(x_5, 0, x_31);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_5);
lean_dec(x_7);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_dec(x_4);
x_34 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_35 = l_unreachable_x21___rarg(x_34);
x_36 = lean_apply_3(x_35, x_1, x_2, x_33);
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
lean_dec(x_5);
if (lean_obj_tag(x_37) == 9)
{
lean_object* x_38; 
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_4, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_40 = x_4;
} else {
 lean_dec_ref(x_4);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = l_Nat_repr(x_41);
x_43 = l_Lean_numLitKind;
x_44 = l_Lean_SourceInfo_inhabited___closed__1;
x_45 = l_Lean_mkStxLit(x_43, x_42, x_44);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_40)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_40;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_49 = x_4;
} else {
 lean_dec_ref(x_4);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_38, 0);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_SourceInfo_inhabited___closed__1;
x_52 = l_Lean_mkStxStrLit(x_50, x_51);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_49;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_37);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_dec(x_4);
x_56 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_57 = l_unreachable_x21___rarg(x_56);
x_58 = lean_apply_3(x_57, x_1, x_2, x_55);
return x_58;
}
}
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabLit), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabLit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__17;
x_4 = l___regBuiltin_Lean_Delaborator_delabLit___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabOfNat___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_5) == 9)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Nat_repr(x_7);
x_9 = l_Lean_numLitKind;
x_10 = l_Lean_SourceInfo_inhabited___closed__1;
x_11 = l_Lean_mkStxLit(x_9, x_8, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
lean_object* _init_l_Lean_Delaborator_delabOfNat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabOfNat___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabOfNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppExplicit___closed__1;
x_2 = l_Lean_Delaborator_delabOfNat___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabOfNat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPCoercions___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabOfNat(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabOfNat___closed__3;
x_5 = l_Lean_Delaborator_delabOfNat___closed__2;
x_6 = l_Lean_Delaborator_whenPPOption(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Delaborator_delabOfNat___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_delabOfNat___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_getExprKind___closed__9;
x_2 = l_Lean_Meta_evalNat___main___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabOfNat), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2;
x_4 = l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Delaborator_delabProj___closed__1() {
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
lean_object* l_Lean_Delaborator_delabProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_getExpr(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 11)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
x_10 = l_Lean_Delaborator_withProj___rarg(x_9, x_1, x_2, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = l_Array_empty___closed__1;
x_23 = lean_array_push(x_22, x_21);
x_24 = l_Lean_Delaborator_delabProj___closed__1;
x_25 = lean_array_push(x_23, x_24);
x_26 = lean_mk_syntax_num_lit(x_8);
x_27 = lean_array_push(x_25, x_26);
x_28 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_11, 0, x_29);
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = l_Array_empty___closed__1;
x_32 = lean_array_push(x_31, x_30);
x_33 = l_Lean_Delaborator_delabProj___closed__1;
x_34 = lean_array_push(x_32, x_33);
x_35 = lean_mk_syntax_num_lit(x_8);
x_36 = lean_array_push(x_34, x_35);
x_37 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_10, 0, x_39);
return x_10;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_dec(x_10);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_42 = x_11;
} else {
 lean_dec_ref(x_11);
 x_42 = lean_box(0);
}
x_43 = l_Array_empty___closed__1;
x_44 = lean_array_push(x_43, x_41);
x_45 = l_Lean_Delaborator_delabProj___closed__1;
x_46 = lean_array_push(x_44, x_45);
x_47 = lean_mk_syntax_num_lit(x_8);
x_48 = lean_array_push(x_46, x_47);
x_49 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
if (lean_is_scalar(x_42)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_42;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_8);
x_53 = !lean_is_exclusive(x_10);
if (x_53 == 0)
{
return x_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_10, 0);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_10);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_6);
x_57 = lean_ctor_get(x_4, 1);
lean_inc(x_57);
lean_dec(x_4);
x_58 = l_Lean_Delaborator_DelabM_inhabited___closed__1;
x_59 = l_unreachable_x21___rarg(x_58);
x_60 = lean_apply_3(x_59, x_1, x_2, x_57);
return x_60;
}
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabProj___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabProj), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabProj(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__21;
x_4 = l___regBuiltin_Lean_Delaborator_delabProj___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabProjectionApp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_Expr_getAppFn___main(x_5);
if (lean_obj_tag(x_6) == 4)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_get_projection_info(x_9, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_15);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_add(x_17, x_173);
x_175 = lean_nat_dec_eq(x_16, x_174);
lean_dec(x_174);
lean_dec(x_16);
if (x_175 == 0)
{
lean_object* x_176; 
x_176 = lean_box(0);
x_18 = x_176;
x_19 = x_4;
goto block_172;
}
else
{
lean_object* x_177; 
x_177 = l_Lean_Meta_commitWhen___lambda__1___closed__1;
x_18 = x_177;
x_19 = x_4;
goto block_172;
}
block_172:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_18);
x_22 = l_Lean_Delaborator_delabAppImplicit___closed__7;
lean_inc(x_2);
x_23 = l_Lean_Delaborator_getPPOption(x_22, x_2, x_3, x_19);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_17);
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
x_29 = l_Lean_Delaborator_withAppArg___rarg(x_28, x_2, x_3, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
lean_dec(x_8);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_29, 0, x_33);
return x_29;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_29, 0);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_30, 0);
x_41 = l_Array_empty___closed__1;
x_42 = lean_array_push(x_41, x_40);
x_43 = l_Lean_Delaborator_delabProj___closed__1;
x_44 = lean_array_push(x_42, x_43);
x_45 = lean_box(0);
x_46 = lean_name_mk_string(x_45, x_8);
x_47 = lean_mk_syntax_ident(x_46);
x_48 = lean_array_push(x_44, x_47);
x_49 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_30, 0, x_50);
return x_29;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_30, 0);
lean_inc(x_51);
lean_dec(x_30);
x_52 = l_Array_empty___closed__1;
x_53 = lean_array_push(x_52, x_51);
x_54 = l_Lean_Delaborator_delabProj___closed__1;
x_55 = lean_array_push(x_53, x_54);
x_56 = lean_box(0);
x_57 = lean_name_mk_string(x_56, x_8);
x_58 = lean_mk_syntax_ident(x_57);
x_59 = lean_array_push(x_55, x_58);
x_60 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_29, 0, x_62);
return x_29;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_63 = lean_ctor_get(x_29, 1);
lean_inc(x_63);
lean_dec(x_29);
x_64 = lean_ctor_get(x_30, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_65 = x_30;
} else {
 lean_dec_ref(x_30);
 x_65 = lean_box(0);
}
x_66 = l_Array_empty___closed__1;
x_67 = lean_array_push(x_66, x_64);
x_68 = l_Lean_Delaborator_delabProj___closed__1;
x_69 = lean_array_push(x_67, x_68);
x_70 = lean_box(0);
x_71 = lean_name_mk_string(x_70, x_8);
x_72 = lean_mk_syntax_ident(x_71);
x_73 = lean_array_push(x_69, x_72);
x_74 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
if (lean_is_scalar(x_65)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_65;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_8);
x_78 = !lean_is_exclusive(x_29);
if (x_78 == 0)
{
return x_29;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_29, 0);
x_80 = lean_ctor_get(x_29, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_29);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_23);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_23, 1);
x_84 = lean_ctor_get(x_23, 0);
lean_dec(x_84);
x_85 = lean_nat_dec_eq(x_17, x_15);
lean_dec(x_17);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_box(0);
lean_ctor_set(x_23, 0, x_86);
return x_23;
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_free_object(x_23);
x_87 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
x_88 = l_Lean_Delaborator_withAppArg___rarg(x_87, x_2, x_3, x_83);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
lean_dec(x_8);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_88, 0, x_92);
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_88, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_89);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_89, 0);
x_100 = l_Array_empty___closed__1;
x_101 = lean_array_push(x_100, x_99);
x_102 = l_Lean_Delaborator_delabProj___closed__1;
x_103 = lean_array_push(x_101, x_102);
x_104 = lean_box(0);
x_105 = lean_name_mk_string(x_104, x_8);
x_106 = lean_mk_syntax_ident(x_105);
x_107 = lean_array_push(x_103, x_106);
x_108 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_89, 0, x_109);
return x_88;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_110 = lean_ctor_get(x_89, 0);
lean_inc(x_110);
lean_dec(x_89);
x_111 = l_Array_empty___closed__1;
x_112 = lean_array_push(x_111, x_110);
x_113 = l_Lean_Delaborator_delabProj___closed__1;
x_114 = lean_array_push(x_112, x_113);
x_115 = lean_box(0);
x_116 = lean_name_mk_string(x_115, x_8);
x_117 = lean_mk_syntax_ident(x_116);
x_118 = lean_array_push(x_114, x_117);
x_119 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_88, 0, x_121);
return x_88;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_122 = lean_ctor_get(x_88, 1);
lean_inc(x_122);
lean_dec(x_88);
x_123 = lean_ctor_get(x_89, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 x_124 = x_89;
} else {
 lean_dec_ref(x_89);
 x_124 = lean_box(0);
}
x_125 = l_Array_empty___closed__1;
x_126 = lean_array_push(x_125, x_123);
x_127 = l_Lean_Delaborator_delabProj___closed__1;
x_128 = lean_array_push(x_126, x_127);
x_129 = lean_box(0);
x_130 = lean_name_mk_string(x_129, x_8);
x_131 = lean_mk_syntax_ident(x_130);
x_132 = lean_array_push(x_128, x_131);
x_133 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_132);
if (lean_is_scalar(x_124)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_124;
}
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_122);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_8);
x_137 = !lean_is_exclusive(x_88);
if (x_137 == 0)
{
return x_88;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_88, 0);
x_139 = lean_ctor_get(x_88, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_88);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_ctor_get(x_23, 1);
lean_inc(x_141);
lean_dec(x_23);
x_142 = lean_nat_dec_eq(x_17, x_15);
lean_dec(x_17);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_141);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = l___private_Lean_Delaborator_2__delabBinders___main___closed__1;
x_146 = l_Lean_Delaborator_withAppArg___rarg(x_145, x_2, x_3, x_141);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_8);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
x_150 = lean_box(0);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_153 = x_146;
} else {
 lean_dec_ref(x_146);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_147, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_155 = x_147;
} else {
 lean_dec_ref(x_147);
 x_155 = lean_box(0);
}
x_156 = l_Array_empty___closed__1;
x_157 = lean_array_push(x_156, x_154);
x_158 = l_Lean_Delaborator_delabProj___closed__1;
x_159 = lean_array_push(x_157, x_158);
x_160 = lean_box(0);
x_161 = lean_name_mk_string(x_160, x_8);
x_162 = lean_mk_syntax_ident(x_161);
x_163 = lean_array_push(x_159, x_162);
x_164 = l_Lean_Parser_Term_proj___elambda__1___closed__1;
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_163);
if (lean_is_scalar(x_155)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_155;
}
lean_ctor_set(x_166, 0, x_165);
if (lean_is_scalar(x_153)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_153;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_152);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_8);
x_168 = lean_ctor_get(x_146, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_146, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_170 = x_146;
} else {
 lean_dec_ref(x_146);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
}
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_box(0);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_4);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_4);
return x_181;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_4);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_4);
return x_185;
}
}
}
lean_object* _init_l_Lean_Delaborator_delabProjectionApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabProjectionApp___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabProjectionApp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppExplicit___closed__1;
x_2 = l_Lean_Delaborator_delabProjectionApp___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Delaborator_delabProjectionApp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPStructureProjections___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_Delaborator_delabProjectionApp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabProjectionApp___closed__3;
x_5 = l_Lean_Delaborator_delabProjectionApp___closed__2;
x_6 = l_Lean_Delaborator_whenPPOption(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Delaborator_delabProjectionApp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_delabProjectionApp___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabProjectionApp), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabProjectionApp(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l_Lean_Delaborator_getExprKind___closed__9;
x_4 = l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabCoe___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_61);
x_63 = lean_unsigned_to_nat(4u);
x_64 = lean_nat_dec_le(x_63, x_62);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_box(0);
x_5 = x_65;
x_6 = x_4;
goto block_60;
}
else
{
lean_object* x_66; 
x_66 = l_Lean_Meta_commitWhen___lambda__1___closed__1;
x_5 = x_66;
x_6 = x_4;
goto block_60;
}
block_60:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = l_Lean_Delaborator_delabAppImplicit(x_2, x_3, x_6);
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_49; uint8_t x_50; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_18 = x_9;
} else {
 lean_dec_ref(x_9);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_49 = l_Lean_mkAppStx___closed__8;
lean_inc(x_19);
x_50 = l_Lean_Syntax_isOfKind(x_19, x_49);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 0;
x_21 = x_51;
goto block_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = l_Lean_Syntax_getArgs(x_19);
x_53 = lean_array_get_size(x_52);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_dec_eq(x_53, x_54);
lean_dec(x_53);
x_21 = x_55;
goto block_48;
}
block_48:
{
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_18;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getArg(x_19, x_24);
lean_dec(x_19);
x_26 = l_Lean_Syntax_getArgs(x_25);
lean_dec(x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_nat_dec_eq(x_27, x_24);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = l_Lean_Syntax_inhabited;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get(x_29, x_26, x_30);
x_32 = l_Array_empty___closed__1;
x_33 = lean_array_push(x_32, x_31);
x_34 = l_Array_eraseIdx___rarg(x_26, x_30);
x_35 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_34, x_34, x_30, x_32);
lean_dec(x_34);
x_36 = l_Lean_nullKind___closed__2;
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_array_push(x_33, x_37);
x_39 = l_Lean_mkAppStx___closed__8;
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
if (lean_is_scalar(x_20)) {
 x_41 = lean_alloc_ctor(1, 1, 0);
} else {
 x_41 = x_20;
}
lean_ctor_set(x_41, 0, x_40);
if (lean_is_scalar(x_18)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_18;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_17);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = l_Lean_Syntax_inhabited;
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_array_get(x_43, x_26, x_44);
lean_dec(x_26);
if (lean_is_scalar(x_20)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_20;
}
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_18)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_18;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_17);
return x_47;
}
}
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_9);
if (x_56 == 0)
{
return x_9;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
lean_object* _init_l_Lean_Delaborator_delabCoe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabCoe___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Delaborator_delabCoe___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_delabAppExplicit___closed__1;
x_2 = l_Lean_Delaborator_delabCoe___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Delaborator_delabAppExplicit___spec__2___rarg), 5, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Delaborator_delabCoe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Delaborator_delabOfNat___closed__3;
x_5 = l_Lean_Delaborator_delabCoe___closed__2;
x_6 = l_Lean_Delaborator_whenPPOption(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Delaborator_delabCoe___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Delaborator_delabCoe___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabCoe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_getExprKind___closed__9;
x_2 = l_Lean_Elab_Term_tryCoe___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabCoe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabCoe), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabCoe(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l___regBuiltin_Lean_Delaborator_delabCoe___closed__1;
x_4 = l___regBuiltin_Lean_Delaborator_delabCoe___closed__2;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Delaborator_delabCoeFun(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Delaborator_delabCoe(x_1, x_2, x_3);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coeFun");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Delaborator_getExprKind___closed__9;
x_2 = l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Delaborator_delabCoeFun), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Delaborator_delabCoeFun(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Delaborator_delabAttribute;
x_3 = l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2;
x_4 = l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_6);
lean_ctor_set(x_8, 3, x_2);
lean_inc(x_3);
x_9 = l_Lean_Delaborator_delab(x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_isClassQuick___main___closed__1;
x_13 = l_unreachable_x21___rarg(x_12);
x_14 = lean_apply_2(x_13, x_3, x_11);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_3);
x_15 = !lean_is_exclusive(x_9);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_9, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_17);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
else
{
uint8_t x_21; 
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_9, 0);
x_23 = lean_ctor_get(x_9, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_9);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_ProjFns(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Delaborator(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Level_quote___main___lambda__1___closed__1 = _init_l_Lean_Level_quote___main___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__1___closed__1);
l_Lean_Level_quote___main___lambda__1___closed__2 = _init_l_Lean_Level_quote___main___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__1___closed__2);
l_Lean_Level_quote___main___lambda__1___closed__3 = _init_l_Lean_Level_quote___main___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__1___closed__3);
l_Lean_Level_quote___main___lambda__1___closed__4 = _init_l_Lean_Level_quote___main___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__1___closed__4);
l_Lean_Level_quote___main___lambda__2___closed__1 = _init_l_Lean_Level_quote___main___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__2___closed__1);
l_Lean_Level_quote___main___lambda__4___closed__1 = _init_l_Lean_Level_quote___main___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__4___closed__1);
l_Lean_Level_quote___main___lambda__4___closed__2 = _init_l_Lean_Level_quote___main___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__4___closed__2);
l_Lean_Level_quote___main___lambda__6___closed__1 = _init_l_Lean_Level_quote___main___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__6___closed__1);
l_Lean_Level_quote___main___lambda__6___closed__2 = _init_l_Lean_Level_quote___main___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__6___closed__2);
l_Lean_Level_quote___main___lambda__9___closed__1 = _init_l_Lean_Level_quote___main___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__9___closed__1);
l_Lean_Level_quote___main___lambda__9___closed__2 = _init_l_Lean_Level_quote___main___lambda__9___closed__2();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__9___closed__2);
l_Lean_Level_quote___main___lambda__9___closed__3 = _init_l_Lean_Level_quote___main___lambda__9___closed__3();
lean_mark_persistent(l_Lean_Level_quote___main___lambda__9___closed__3);
l_Lean_Level_quote___main___closed__1 = _init_l_Lean_Level_quote___main___closed__1();
lean_mark_persistent(l_Lean_Level_quote___main___closed__1);
l_Lean_Level_quote___main___closed__2 = _init_l_Lean_Level_quote___main___closed__2();
lean_mark_persistent(l_Lean_Level_quote___main___closed__2);
l_Lean_Level_quote___main___closed__3 = _init_l_Lean_Level_quote___main___closed__3();
lean_mark_persistent(l_Lean_Level_quote___main___closed__3);
l_Lean_Level_quote___main___closed__4 = _init_l_Lean_Level_quote___main___closed__4();
lean_mark_persistent(l_Lean_Level_quote___main___closed__4);
l_Lean_Level_quote___main___closed__5 = _init_l_Lean_Level_quote___main___closed__5();
lean_mark_persistent(l_Lean_Level_quote___main___closed__5);
l_Lean_Level_quote___main___closed__6 = _init_l_Lean_Level_quote___main___closed__6();
lean_mark_persistent(l_Lean_Level_quote___main___closed__6);
l_Lean_Level_HasQuote___closed__1 = _init_l_Lean_Level_HasQuote___closed__1();
lean_mark_persistent(l_Lean_Level_HasQuote___closed__1);
l_Lean_Level_HasQuote = _init_l_Lean_Level_HasQuote();
lean_mark_persistent(l_Lean_Level_HasQuote);
l_Lean_getPPBinderTypes___closed__1 = _init_l_Lean_getPPBinderTypes___closed__1();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__1);
l_Lean_getPPBinderTypes___closed__2 = _init_l_Lean_getPPBinderTypes___closed__2();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__2);
l_Lean_getPPBinderTypes___closed__3 = _init_l_Lean_getPPBinderTypes___closed__3();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__3);
l_Lean_getPPBinderTypes___closed__4 = _init_l_Lean_getPPBinderTypes___closed__4();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__4);
l_Lean_getPPCoercions___closed__1 = _init_l_Lean_getPPCoercions___closed__1();
lean_mark_persistent(l_Lean_getPPCoercions___closed__1);
l_Lean_getPPCoercions___closed__2 = _init_l_Lean_getPPCoercions___closed__2();
lean_mark_persistent(l_Lean_getPPCoercions___closed__2);
l_Lean_getPPExplicit___closed__1 = _init_l_Lean_getPPExplicit___closed__1();
lean_mark_persistent(l_Lean_getPPExplicit___closed__1);
l_Lean_getPPStructureProjections___closed__1 = _init_l_Lean_getPPStructureProjections___closed__1();
lean_mark_persistent(l_Lean_getPPStructureProjections___closed__1);
l_Lean_getPPStructureProjections___closed__2 = _init_l_Lean_getPPStructureProjections___closed__2();
lean_mark_persistent(l_Lean_getPPStructureProjections___closed__2);
l_Lean_getPPUniverses___closed__1 = _init_l_Lean_getPPUniverses___closed__1();
lean_mark_persistent(l_Lean_getPPUniverses___closed__1);
l_Lean_getPPAll___closed__1 = _init_l_Lean_getPPAll___closed__1();
lean_mark_persistent(l_Lean_getPPAll___closed__1);
l_Lean_getPPAll___closed__2 = _init_l_Lean_getPPAll___closed__2();
lean_mark_persistent(l_Lean_getPPAll___closed__2);
l_Lean_ppOptions___closed__1 = _init_l_Lean_ppOptions___closed__1();
lean_mark_persistent(l_Lean_ppOptions___closed__1);
l_Lean_ppOptions___closed__2 = _init_l_Lean_ppOptions___closed__2();
lean_mark_persistent(l_Lean_ppOptions___closed__2);
res = l_Lean_ppOptions(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_DelabM_inhabited___closed__1 = _init_l_Lean_Delaborator_DelabM_inhabited___closed__1();
lean_mark_persistent(l_Lean_Delaborator_DelabM_inhabited___closed__1);
l_Lean_Delaborator_DelabM_monadQuotation___closed__1 = _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__1();
lean_mark_persistent(l_Lean_Delaborator_DelabM_monadQuotation___closed__1);
l_Lean_Delaborator_DelabM_monadQuotation___closed__2 = _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__2();
lean_mark_persistent(l_Lean_Delaborator_DelabM_monadQuotation___closed__2);
l_Lean_Delaborator_DelabM_monadQuotation___closed__3 = _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__3();
lean_mark_persistent(l_Lean_Delaborator_DelabM_monadQuotation___closed__3);
l_Lean_Delaborator_DelabM_monadQuotation___closed__4 = _init_l_Lean_Delaborator_DelabM_monadQuotation___closed__4();
lean_mark_persistent(l_Lean_Delaborator_DelabM_monadQuotation___closed__4);
l_Lean_Delaborator_DelabM_monadQuotation = _init_l_Lean_Delaborator_DelabM_monadQuotation();
lean_mark_persistent(l_Lean_Delaborator_DelabM_monadQuotation);
l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1 = _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__1);
l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2 = _init_l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___lambda__1___closed__2);
l_Lean_Delaborator_mkDelabAttribute___closed__1 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__1();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__1);
l_Lean_Delaborator_mkDelabAttribute___closed__2 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__2();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__2);
l_Lean_Delaborator_mkDelabAttribute___closed__3 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__3();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__3);
l_Lean_Delaborator_mkDelabAttribute___closed__4 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__4();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__4);
l_Lean_Delaborator_mkDelabAttribute___closed__5 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__5();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__5);
l_Lean_Delaborator_mkDelabAttribute___closed__6 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__6();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__6);
l_Lean_Delaborator_mkDelabAttribute___closed__7 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__7();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__7);
l_Lean_Delaborator_mkDelabAttribute___closed__8 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__8();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__8);
l_Lean_Delaborator_mkDelabAttribute___closed__9 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__9();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__9);
l_Lean_Delaborator_mkDelabAttribute___closed__10 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__10();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__10);
l_Lean_Delaborator_mkDelabAttribute___closed__11 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__11();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__11);
l_Lean_Delaborator_mkDelabAttribute___closed__12 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__12();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__12);
l_Lean_Delaborator_mkDelabAttribute___closed__13 = _init_l_Lean_Delaborator_mkDelabAttribute___closed__13();
lean_mark_persistent(l_Lean_Delaborator_mkDelabAttribute___closed__13);
l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3 = _init_l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3();
lean_mark_persistent(l_Std_PersistentHashMap_empty___at_Lean_Delaborator_delabAttribute___spec__3);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__1);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1___closed__2);
l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1 = _init_l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1();
lean_mark_persistent(l_Lean_SMap_empty___at_Lean_Delaborator_delabAttribute___spec__1);
l_Lean_Delaborator_delabAttribute___closed__1 = _init_l_Lean_Delaborator_delabAttribute___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__1);
l_Lean_Delaborator_delabAttribute___closed__2 = _init_l_Lean_Delaborator_delabAttribute___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__2);
l_Lean_Delaborator_delabAttribute___closed__3 = _init_l_Lean_Delaborator_delabAttribute___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__3);
l_Lean_Delaborator_delabAttribute___closed__4 = _init_l_Lean_Delaborator_delabAttribute___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__4);
l_Lean_Delaborator_delabAttribute___closed__5 = _init_l_Lean_Delaborator_delabAttribute___closed__5();
lean_mark_persistent(l_Lean_Delaborator_delabAttribute___closed__5);
res = l_Lean_Delaborator_mkDelabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Delaborator_delabAttribute);
lean_dec_ref(res);
l_Lean_Delaborator_getExprKind___closed__1 = _init_l_Lean_Delaborator_getExprKind___closed__1();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__1);
l_Lean_Delaborator_getExprKind___closed__2 = _init_l_Lean_Delaborator_getExprKind___closed__2();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__2);
l_Lean_Delaborator_getExprKind___closed__3 = _init_l_Lean_Delaborator_getExprKind___closed__3();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__3);
l_Lean_Delaborator_getExprKind___closed__4 = _init_l_Lean_Delaborator_getExprKind___closed__4();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__4);
l_Lean_Delaborator_getExprKind___closed__5 = _init_l_Lean_Delaborator_getExprKind___closed__5();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__5);
l_Lean_Delaborator_getExprKind___closed__6 = _init_l_Lean_Delaborator_getExprKind___closed__6();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__6);
l_Lean_Delaborator_getExprKind___closed__7 = _init_l_Lean_Delaborator_getExprKind___closed__7();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__7);
l_Lean_Delaborator_getExprKind___closed__8 = _init_l_Lean_Delaborator_getExprKind___closed__8();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__8);
l_Lean_Delaborator_getExprKind___closed__9 = _init_l_Lean_Delaborator_getExprKind___closed__9();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__9);
l_Lean_Delaborator_getExprKind___closed__10 = _init_l_Lean_Delaborator_getExprKind___closed__10();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__10);
l_Lean_Delaborator_getExprKind___closed__11 = _init_l_Lean_Delaborator_getExprKind___closed__11();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__11);
l_Lean_Delaborator_getExprKind___closed__12 = _init_l_Lean_Delaborator_getExprKind___closed__12();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__12);
l_Lean_Delaborator_getExprKind___closed__13 = _init_l_Lean_Delaborator_getExprKind___closed__13();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__13);
l_Lean_Delaborator_getExprKind___closed__14 = _init_l_Lean_Delaborator_getExprKind___closed__14();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__14);
l_Lean_Delaborator_getExprKind___closed__15 = _init_l_Lean_Delaborator_getExprKind___closed__15();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__15);
l_Lean_Delaborator_getExprKind___closed__16 = _init_l_Lean_Delaborator_getExprKind___closed__16();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__16);
l_Lean_Delaborator_getExprKind___closed__17 = _init_l_Lean_Delaborator_getExprKind___closed__17();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__17);
l_Lean_Delaborator_getExprKind___closed__18 = _init_l_Lean_Delaborator_getExprKind___closed__18();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__18);
l_Lean_Delaborator_getExprKind___closed__19 = _init_l_Lean_Delaborator_getExprKind___closed__19();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__19);
l_Lean_Delaborator_getExprKind___closed__20 = _init_l_Lean_Delaborator_getExprKind___closed__20();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__20);
l_Lean_Delaborator_getExprKind___closed__21 = _init_l_Lean_Delaborator_getExprKind___closed__21();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__21);
l_Lean_Delaborator_getExprKind___closed__22 = _init_l_Lean_Delaborator_getExprKind___closed__22();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__22);
l_Lean_Delaborator_getExprKind___closed__23 = _init_l_Lean_Delaborator_getExprKind___closed__23();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__23);
l_Lean_Delaborator_getExprKind___closed__24 = _init_l_Lean_Delaborator_getExprKind___closed__24();
lean_mark_persistent(l_Lean_Delaborator_getExprKind___closed__24);
l_Lean_Delaborator_getPPOption___closed__1 = _init_l_Lean_Delaborator_getPPOption___closed__1();
lean_mark_persistent(l_Lean_Delaborator_getPPOption___closed__1);
l_Lean_Delaborator_delab___closed__1 = _init_l_Lean_Delaborator_delab___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delab___closed__1);
l_Lean_Delaborator_delab___closed__2 = _init_l_Lean_Delaborator_delab___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delab___closed__2);
l_Lean_Delaborator_delab___closed__3 = _init_l_Lean_Delaborator_delab___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delab___closed__3);
l___regBuiltin_Lean_Delaborator_delabFVar___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabFVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabFVar___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabFVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabMVar___closed__1 = _init_l_Lean_Delaborator_delabMVar___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabMVar___closed__1);
l_Lean_Delaborator_delabMVar___closed__2 = _init_l_Lean_Delaborator_delabMVar___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabMVar___closed__2);
l___regBuiltin_Lean_Delaborator_delabMVar___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabMVar___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabMVar___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabSort___closed__1 = _init_l_Lean_Delaborator_delabSort___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__1);
l_Lean_Delaborator_delabSort___closed__2 = _init_l_Lean_Delaborator_delabSort___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__2);
l_Lean_Delaborator_delabSort___closed__3 = _init_l_Lean_Delaborator_delabSort___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__3);
l_Lean_Delaborator_delabSort___closed__4 = _init_l_Lean_Delaborator_delabSort___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__4);
l_Lean_Delaborator_delabSort___closed__5 = _init_l_Lean_Delaborator_delabSort___closed__5();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__5);
l_Lean_Delaborator_delabSort___closed__6 = _init_l_Lean_Delaborator_delabSort___closed__6();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__6);
l_Lean_Delaborator_delabSort___closed__7 = _init_l_Lean_Delaborator_delabSort___closed__7();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__7);
l_Lean_Delaborator_delabSort___closed__8 = _init_l_Lean_Delaborator_delabSort___closed__8();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__8);
l_Lean_Delaborator_delabSort___closed__9 = _init_l_Lean_Delaborator_delabSort___closed__9();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__9);
l_Lean_Delaborator_delabSort___closed__10 = _init_l_Lean_Delaborator_delabSort___closed__10();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__10);
l_Lean_Delaborator_delabSort___closed__11 = _init_l_Lean_Delaborator_delabSort___closed__11();
lean_mark_persistent(l_Lean_Delaborator_delabSort___closed__11);
l___regBuiltin_Lean_Delaborator_delabSort___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabSort___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabSort___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabSort(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabConst___closed__1 = _init_l_Lean_Delaborator_delabConst___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabConst___closed__1);
l_Lean_Delaborator_delabConst___closed__2 = _init_l_Lean_Delaborator_delabConst___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabConst___closed__2);
l_Lean_Delaborator_delabConst___closed__3 = _init_l_Lean_Delaborator_delabConst___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabConst___closed__3);
l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__1);
l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Delaborator_getImplicitParams___spec__1___closed__2);
l_Lean_Delaborator_getImplicitParams___closed__1 = _init_l_Lean_Delaborator_getImplicitParams___closed__1();
lean_mark_persistent(l_Lean_Delaborator_getImplicitParams___closed__1);
l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1 = _init_l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__1);
l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2 = _init_l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___lambda__1___closed__2);
l_Lean_Delaborator_delabAppExplicit___closed__1 = _init_l_Lean_Delaborator_delabAppExplicit___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___closed__1);
l_Lean_Delaborator_delabAppExplicit___closed__2 = _init_l_Lean_Delaborator_delabAppExplicit___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___closed__2);
l_Lean_Delaborator_delabAppExplicit___closed__3 = _init_l_Lean_Delaborator_delabAppExplicit___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___closed__3);
l_Lean_Delaborator_delabAppExplicit___closed__4 = _init_l_Lean_Delaborator_delabAppExplicit___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabAppExplicit___closed__4);
l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabAppExplicit___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabAppExplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabAppImplicit___closed__1 = _init_l_Lean_Delaborator_delabAppImplicit___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__1);
l_Lean_Delaborator_delabAppImplicit___closed__2 = _init_l_Lean_Delaborator_delabAppImplicit___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__2);
l_Lean_Delaborator_delabAppImplicit___closed__3 = _init_l_Lean_Delaborator_delabAppImplicit___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__3);
l_Lean_Delaborator_delabAppImplicit___closed__4 = _init_l_Lean_Delaborator_delabAppImplicit___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__4);
l_Lean_Delaborator_delabAppImplicit___closed__5 = _init_l_Lean_Delaborator_delabAppImplicit___closed__5();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__5);
l_Lean_Delaborator_delabAppImplicit___closed__6 = _init_l_Lean_Delaborator_delabAppImplicit___closed__6();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__6);
l_Lean_Delaborator_delabAppImplicit___closed__7 = _init_l_Lean_Delaborator_delabAppImplicit___closed__7();
lean_mark_persistent(l_Lean_Delaborator_delabAppImplicit___closed__7);
l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabAppImplicit___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabAppImplicit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1 = _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1();
lean_mark_persistent(l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__1);
l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2 = _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2();
lean_mark_persistent(l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__2);
l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3 = _init_l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3();
lean_mark_persistent(l___private_Lean_Delaborator_1__shouldGroupWithNext___closed__3);
l___private_Lean_Delaborator_2__delabBinders___main___closed__1 = _init_l___private_Lean_Delaborator_2__delabBinders___main___closed__1();
lean_mark_persistent(l___private_Lean_Delaborator_2__delabBinders___main___closed__1);
l_Lean_Delaborator_delabLam___lambda__1___closed__1 = _init_l_Lean_Delaborator_delabLam___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabLam___lambda__1___closed__1);
l_Lean_Delaborator_delabLam___lambda__1___closed__2 = _init_l_Lean_Delaborator_delabLam___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabLam___lambda__1___closed__2);
l_Lean_Delaborator_delabLam___lambda__1___closed__3 = _init_l_Lean_Delaborator_delabLam___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabLam___lambda__1___closed__3);
l_Lean_Delaborator_delabLam___lambda__1___closed__4 = _init_l_Lean_Delaborator_delabLam___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Delaborator_delabLam___lambda__1___closed__4);
l_Lean_Delaborator_delabLam___closed__1 = _init_l_Lean_Delaborator_delabLam___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabLam___closed__1);
l___regBuiltin_Lean_Delaborator_delabLam___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabLam___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabLam___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabLam(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1 = _init_l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Delaborator_delabForall___spec__2___closed__1);
l_Lean_Delaborator_delabForall___closed__1 = _init_l_Lean_Delaborator_delabForall___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabForall___closed__1);
l___regBuiltin_Lean_Delaborator_delabForall___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabForall___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabForall___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabForall(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Delaborator_delabLit___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabLit___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabLit___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabLit(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabOfNat___closed__1 = _init_l_Lean_Delaborator_delabOfNat___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabOfNat___closed__1);
l_Lean_Delaborator_delabOfNat___closed__2 = _init_l_Lean_Delaborator_delabOfNat___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabOfNat___closed__2);
l_Lean_Delaborator_delabOfNat___closed__3 = _init_l_Lean_Delaborator_delabOfNat___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabOfNat___closed__3);
l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabOfNat___closed__1);
l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2 = _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabOfNat___closed__2);
l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3 = _init_l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabOfNat___closed__3);
res = l___regBuiltin_Lean_Delaborator_delabOfNat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabProj___closed__1 = _init_l_Lean_Delaborator_delabProj___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabProj___closed__1);
l___regBuiltin_Lean_Delaborator_delabProj___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabProj___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabProj___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabProj(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabProjectionApp___closed__1 = _init_l_Lean_Delaborator_delabProjectionApp___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabProjectionApp___closed__1);
l_Lean_Delaborator_delabProjectionApp___closed__2 = _init_l_Lean_Delaborator_delabProjectionApp___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabProjectionApp___closed__2);
l_Lean_Delaborator_delabProjectionApp___closed__3 = _init_l_Lean_Delaborator_delabProjectionApp___closed__3();
lean_mark_persistent(l_Lean_Delaborator_delabProjectionApp___closed__3);
l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabProjectionApp___closed__1);
res = l___regBuiltin_Lean_Delaborator_delabProjectionApp(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Delaborator_delabCoe___closed__1 = _init_l_Lean_Delaborator_delabCoe___closed__1();
lean_mark_persistent(l_Lean_Delaborator_delabCoe___closed__1);
l_Lean_Delaborator_delabCoe___closed__2 = _init_l_Lean_Delaborator_delabCoe___closed__2();
lean_mark_persistent(l_Lean_Delaborator_delabCoe___closed__2);
l___regBuiltin_Lean_Delaborator_delabCoe___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabCoe___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabCoe___closed__1);
l___regBuiltin_Lean_Delaborator_delabCoe___closed__2 = _init_l___regBuiltin_Lean_Delaborator_delabCoe___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabCoe___closed__2);
res = l___regBuiltin_Lean_Delaborator_delabCoe(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1 = _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__1);
l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2 = _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__2);
l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3 = _init_l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Delaborator_delabCoeFun___closed__3);
res = l___regBuiltin_Lean_Delaborator_delabCoeFun(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
