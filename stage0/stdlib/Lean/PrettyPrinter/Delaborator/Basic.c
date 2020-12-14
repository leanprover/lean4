// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Basic
// Imports: Init Lean.KeyedDeclsAttribute Lean.ProjFns Lean.Syntax Lean.Meta.Match Lean.Elab.Term
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
extern lean_object* l_Lean_Expr_ctorName___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__1;
lean_object* l_Lean_Level_quote___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFailureId;
extern lean_object* l_Lean_Syntax_strLitToAtom___closed__3;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
extern lean_object* l_precMax___closed__3;
lean_object* l_Lean_PrettyPrinter_delab___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3;
uint8_t l_Lean_getPPCoercions(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
lean_object* l_Lean_getPPStructureProjections___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPExplicit(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPNotation___boxed(lean_object*);
lean_object* l_Lean_Level_quote___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_getPPNotation___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_descend(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__1;
lean_object* l_Lean_Level_quote___lambda__6___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KeyedDeclsAttribute_Def_evalKey___default___rarg___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__8;
lean_object* l_ReaderT_bind___at_Lean_Level_quote___spec__1(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607_(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Level_quote___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
lean_object* l_Lean_Level_quote___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPStructureProjections(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote_match__1(lean_object*);
lean_object* l_Lean_getPPFullNames___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__4___closed__2;
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPFullNames___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
lean_object* l_Lean_Level_quote_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1(lean_object*);
uint8_t l_Lean_getPPUniverses(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(lean_object*, size_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1(lean_object*);
lean_object* l_Lean_Level_quote___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedException___closed__1;
uint8_t l_Lean_getPPBinderTypes(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_object*);
uint8_t l_Lean_getPPFullNames(lean_object*);
lean_object* l_Lean_Level_instQuoteLevel___closed__1;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_Context_pos___default;
lean_object* l_Lean_Level_quote___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Level_LevelToFormat_Result_format___closed__3;
extern lean_object* l_Lean_numLitKind;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_905____closed__4;
lean_object* l_Lean_Level_quote___lambda__9___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPUnicode___boxed(lean_object*);
lean_object* l_Lean_getPPUnicode___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Expr_ctorName___closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1(lean_object*);
lean_object* l_Lean_Level_quote___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
extern lean_object* l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_340____closed__3;
lean_object* l_Lean_Level_quote_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_toNat(lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object*);
extern lean_object* l_Lean_instInhabitedSourceInfo___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_340____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__2___closed__1;
uint8_t l_Lean_getPPStructureInstanceType(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPUnicode(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
extern lean_object* l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2(lean_object*);
lean_object* l_Lean_attrParamSyntaxToIdentifier(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2;
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1;
lean_object* l_Lean_Level_quote___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__9(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureInstances___closed__2;
extern lean_object* l_Lean_Elab_Level_elabLevel___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object*);
uint8_t l_Lean_getPPPrivateNames(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Format_getUnicode___closed__1;
lean_object* l_Lean_Level_quote___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPStructureInstances(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn(lean_object*);
lean_object* l_Lean_getPPCoercions___closed__2;
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote_match__2(lean_object*);
lean_object* l_Lean_getPPCoercions___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_340____closed__1;
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Level_quote___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPCoercions___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4;
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
extern lean_object* l_Lean_Expr_ctorName___closed__9;
uint8_t l_Lean_getPPNotation(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr(lean_object*);
lean_object* l_Lean_fmt___at_Lean_ppExpr___spec__4(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureInstanceType___boxed(lean_object*);
lean_object* l_Lean_getPPStructureInstanceType___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__10;
lean_object* l_Lean_Level_quote___lambda__4___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg(lean_object*);
extern lean_object* l_myMacro____x40_Init_NotationExtra___hyg_3453____closed__43;
lean_object* l_Lean_Level_instQuoteLevel;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
lean_object* l_Lean_Level_quote___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Level_elabLevel___closed__5;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_getPPUniverses___closed__2;
lean_object* l_Lean_PrettyPrinter_delab___closed__6;
extern lean_object* l_Lean_getSanitizeNames___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2(lean_object*);
lean_object* l_Array_appendCore___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Level_elabLevel___closed__3;
lean_object* l_Lean_getPPAll___boxed(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
lean_object* l_Lean_Level_quote___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPAll___closed__1;
lean_object* l_Lean_getPPStructureInstances___boxed(lean_object*);
lean_object* l_Lean_getPPUniverses___closed__1;
lean_object* l_Lean_getPPUniverses___boxed(lean_object*);
lean_object* l_Lean_getPPStructureInstances___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPFullNames___closed__2;
lean_object* lean_nat_mul(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__28;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
lean_object* l_Lean_getPPStructureInstanceType___closed__2;
lean_object* l_Lean_getPPExplicit___boxed(lean_object*);
lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPPrivateNames___closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554_(lean_object*);
extern lean_object* l_stx___x2b___closed__3;
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs(lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__36;
lean_object* l_Lean_getPPNotation___closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2;
lean_object* l_Lean_getPPExplicit___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
uint8_t l_Lean_Expr_binderInfo(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
extern lean_object* l_Lean_Expr_ctorName___closed__6;
lean_object* l_Lean_Level_quote___closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_762____closed__4;
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2038_(lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPBinderTypes___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2;
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PrettyPrinter_delab___closed__5;
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPAll(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___closed__1;
lean_object* l_Lean_Level_quote___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6;
lean_object* l_Lean_getPPPrivateNames___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1(lean_object*);
lean_object* l_Lean_getPPStructureProjections___closed__2;
lean_object* l_Lean_Level_quote(lean_object*);
lean_object* l_Lean_Level_quote___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1;
lean_object* l_Lean_getPPPrivateNames___boxed(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3;
lean_object* l_Lean_getPPStructureProjections___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg(lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption_match__1(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPBinderTypes___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_mkLit(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Level_quote___lambda__6___closed__2;
lean_object* l_Lean_PrettyPrinter_delab___closed__1;
lean_object* l_Lean_getPPBinderTypes___boxed(lean_object*);
lean_object* l_Lean_Level_quote_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Level_quote_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_quote_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Level_quote_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_13 = lean_box_uint64(x_12);
x_14 = lean_apply_3(x_3, x_1, x_11, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_18 = lean_box_uint64(x_17);
x_19 = lean_apply_3(x_4, x_15, x_16, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_23 = lean_box_uint64(x_22);
x_24 = lean_apply_3(x_5, x_20, x_21, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_27 = lean_box_uint64(x_26);
x_28 = lean_apply_2(x_6, x_25, x_27);
return x_28;
}
default: 
{
lean_object* x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_31 = lean_box_uint64(x_30);
x_32 = lean_apply_2(x_7, x_29, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Level_quote_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Level_quote_match__2___rarg), 7, 0);
return x_2;
}
}
lean_object* l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
}
lean_object* l_ReaderT_bind___at_Lean_Level_quote___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Level_quote___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_762____closed__4;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_quote___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSourceInfo___closed__1;
x_2 = l_stx___x2b___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = l_Lean_Level_getLevelOffset(x_1);
x_6 = l_Lean_Level_quote(x_5);
x_7 = l_Array_empty___closed__1;
x_8 = lean_array_push(x_7, x_6);
x_9 = l_Lean_Level_quote___lambda__2___closed__1;
x_10 = lean_array_push(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Level_getOffsetAux(x_1, x_11);
x_13 = l_Nat_repr(x_12);
x_14 = l_Lean_numLitKind;
x_15 = l_Lean_instInhabitedSourceInfo___closed__1;
x_16 = l_Lean_Syntax_mkLit(x_14, x_13, x_15);
x_17 = lean_array_push(x_10, x_16);
x_18 = l_Lean_Elab_Level_elabLevel___closed__5;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
lean_object* l_Lean_Level_quote___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Nat_repr(x_1);
x_6 = l_Lean_numLitKind;
x_7 = l_Lean_instInhabitedSourceInfo___closed__1;
x_8 = l_Lean_Syntax_mkLit(x_6, x_5, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
static lean_object* _init_l_Lean_Level_quote___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSourceInfo___closed__1;
x_2 = l_precMax___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_quote___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___lambda__4___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___lambda__4___closed__2;
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
lean_object* l_Lean_Level_quote___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Array_appendCore___rarg(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___lambda__4___closed__2;
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
static lean_object* _init_l_Lean_Level_quote___lambda__6___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedSourceInfo___closed__1;
x_2 = l_Lean_Level_LevelToFormat_Result_format___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_quote___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Level_quote___lambda__6___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Level_quote___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___lambda__6___closed__2;
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
lean_object* l_Lean_Level_quote___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = l_Lean_Level_quote(x_1);
x_8 = l_Array_empty___closed__1;
x_9 = lean_array_push(x_8, x_7);
x_10 = l_Array_appendCore___rarg(x_9, x_2);
x_11 = l_Lean_nullKind___closed__2;
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Level_quote___lambda__6___closed__2;
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
lean_object* l_Lean_Level_quote___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Level_quote___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__36;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__1___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_2 = l_Lean_Level_quote___closed__1;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_quote___closed__2;
x_2 = l_Lean_Unhygienic_run___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__9___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_2 = l_Lean_Level_quote___closed__4;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Level_quote___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Level_quote___closed__5;
x_2 = l_Lean_Unhygienic_run___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_Level_quote(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = l_Lean_Level_quote___closed__3;
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = l_Lean_Level_toNat(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__2___boxed), 4, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_6 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
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
x_9 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__3___boxed), 4, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_9);
x_12 = l_Lean_Unhygienic_run___rarg(x_11);
return x_12;
}
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Level_quote(x_14);
x_16 = l_Lean_Elab_Level_elabLevel___closed__2;
lean_inc(x_15);
x_17 = l_Lean_Syntax_isOfKind(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__4___boxed), 6, 3);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_15);
lean_closure_set(x_18, 2, x_16);
x_19 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_18);
x_21 = l_Lean_Unhygienic_run___rarg(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = l_Lean_Syntax_getArg(x_15, x_22);
lean_dec(x_15);
x_24 = l_Lean_Syntax_getArgs(x_23);
lean_dec(x_23);
x_25 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__5___boxed), 6, 3);
lean_closure_set(x_25, 0, x_13);
lean_closure_set(x_25, 1, x_24);
lean_closure_set(x_25, 2, x_16);
x_26 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_27 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_25);
x_28 = l_Lean_Unhygienic_run___rarg(x_27);
return x_28;
}
}
case 3:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lean_Level_quote(x_30);
x_32 = l_Lean_Elab_Level_elabLevel___closed__3;
lean_inc(x_31);
x_33 = l_Lean_Syntax_isOfKind(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__6___boxed), 6, 3);
lean_closure_set(x_34, 0, x_29);
lean_closure_set(x_34, 1, x_31);
lean_closure_set(x_34, 2, x_32);
x_35 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_34);
x_37 = l_Lean_Unhygienic_run___rarg(x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = l_Lean_Syntax_getArg(x_31, x_38);
lean_dec(x_31);
x_40 = l_Lean_Syntax_getArgs(x_39);
lean_dec(x_39);
x_41 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__7___boxed), 6, 3);
lean_closure_set(x_41, 0, x_29);
lean_closure_set(x_41, 1, x_40);
lean_closure_set(x_41, 2, x_32);
x_42 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_43 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_43, 0, x_42);
lean_closure_set(x_43, 1, x_41);
x_44 = l_Lean_Unhygienic_run___rarg(x_43);
return x_44;
}
}
case 4:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_alloc_closure((void*)(l_Lean_Level_quote___lambda__8___boxed), 4, 1);
lean_closure_set(x_46, 0, x_45);
x_47 = l_Lean_Unhygienic_instMonadQuotationUnhygienic___closed__4;
x_48 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Level_quote___spec__1___rarg), 4, 2);
lean_closure_set(x_48, 0, x_47);
lean_closure_set(x_48, 1, x_46);
x_49 = l_Lean_Unhygienic_run___rarg(x_48);
return x_49;
}
default: 
{
lean_object* x_50; 
lean_dec(x_1);
x_50 = l_Lean_Level_quote___closed__6;
return x_50;
}
}
}
}
lean_object* l_Lean_Level_quote___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_quote___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Level_quote___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___lambda__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Level_quote___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_quote___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Level_quote___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Level_quote___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Lean_Level_quote___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Level_quote___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Level_quote___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Level_quote___lambda__8(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Level_quote___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Level_quote___lambda__9(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Level_instQuoteLevel___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Level_quote), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Level_instQuoteLevel() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Level_instQuoteLevel___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_getPPBinderTypes___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binder_types");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPBinderTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPBinderTypes___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPBinderTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPBinderTypes___closed__2;
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
static lean_object* _init_l_Lean_getPPCoercions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coercions");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPCoercions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
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
static lean_object* _init_l_Lean_getPPExplicit___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_myMacro____x40_Init_NotationExtra___hyg_3453____closed__43;
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
static lean_object* _init_l_Lean_getPPNotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("notation");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPNotation___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPNotation___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPNotation(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPNotation___closed__2;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPNotation___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPNotation(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPStructureProjections___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_projections");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPStructureProjections___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
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
static lean_object* _init_l_Lean_getPPStructureInstances___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_instances");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPStructureInstances___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPStructureInstances___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPStructureInstances(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPStructureInstances___closed__2;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPStructureInstances___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPStructureInstances(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPStructureInstanceType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_instance_type");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPStructureInstanceType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPStructureInstanceType___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPStructureInstanceType(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPStructureInstanceType___closed__2;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPStructureInstanceType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPStructureInstanceType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPUniverses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("universes");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPUniverses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPUniverses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPUniverses(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPUniverses___closed__2;
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
static lean_object* _init_l_Lean_getPPFullNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("full_names");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPFullNames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPFullNames___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPFullNames(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPFullNames___closed__2;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPFullNames___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPFullNames(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPPrivateNames___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private_names");
return x_1;
}
}
static lean_object* _init_l_Lean_getPPPrivateNames___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_getPPPrivateNames___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPPrivateNames(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPPrivateNames___closed__2;
x_3 = 0;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPPrivateNames___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPPrivateNames(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPUnicode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_Format_getUnicode___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPUnicode(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPUnicode___closed__1;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_getPPUnicode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPUnicode(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_getPPAll___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l___private_Lean_Compiler_ExternAttr_0__Lean_syntaxToExternAttrData___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPAll(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_getPPAll___closed__1;
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
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display implicit arguments");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display type of structure instances");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Util_PPExt___hyg_3____closed__8;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPExplicit___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2;
x_4 = lean_register_option(x_2, x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_getPPStructureInstanceType___closed__2;
x_7 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4;
x_8 = lean_register_option(x_6, x_7, x_5);
return x_8;
}
else
{
uint8_t x_9; 
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_Context_pos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabFailure");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedException___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_10);
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_9, 1);
x_17 = lean_ctor_get(x_9, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_20 = lean_nat_dec_eq(x_19, x_18);
lean_dec(x_18);
if (x_20 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_21; 
lean_free_object(x_9);
lean_dec(x_10);
x_21 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_16);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
x_24 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_10);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_10);
x_27 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_22);
return x_27;
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_orElse___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_failure___rarg), 1, 0);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_failure(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
x_20 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_21 = lean_nat_dec_eq(x_20, x_19);
lean_dec(x_19);
if (x_21 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_22; 
lean_free_object(x_10);
lean_dec(x_11);
x_22 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
x_25 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_26 = lean_nat_dec_eq(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_11);
x_28 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_28;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
x_4 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_orElse___rarg), 8, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1;
return x_2;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
return x_1;
}
}
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_attrParamSyntaxToIdentifier(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_KeyedDeclsAttribute_Def_evalKey___default___rarg___closed__3;
x_8 = l_Lean_throwError___at_Lean_KeyedDeclsAttribute_Def_evalKey___default___spec__1(x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("builtinDelab");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delab");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PrettyPrinter");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_340____closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delaborator");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delab");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register a delaborator.\n\n  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`\n  constructor `k`. Multiple delaborators for a single constructor are tried in turn until\n  the first success. If the term to be delaborated is an application of a constant `c`,\n  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")\n  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`\n  is tried first.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
x_4 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
x_5 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
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
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_14; uint64_t x_15; lean_object* x_16; lean_object* x_17; 
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
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_16 = lean_box_uint64(x_15);
x_17 = lean_apply_2(x_2, x_14, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
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
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_20 = lean_box_uint64(x_19);
x_21 = lean_apply_2(x_3, x_18, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_24 = lean_box_uint64(x_23);
x_25 = lean_apply_2(x_4, x_22, x_24);
return x_25;
}
case 3:
{
lean_object* x_26; uint64_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_28 = lean_box_uint64(x_27);
x_29 = lean_apply_2(x_5, x_26, x_28);
return x_29;
}
case 4:
{
lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_33 = lean_box_uint64(x_32);
x_34 = lean_apply_3(x_6, x_30, x_31, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_38 = lean_box_uint64(x_37);
x_39 = lean_apply_3(x_7, x_35, x_36, x_38);
return x_39;
}
case 6:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; lean_object* x_45; 
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
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_44 = lean_box_uint64(x_43);
x_45 = lean_apply_4(x_8, x_40, x_41, x_42, x_44);
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_50 = lean_box_uint64(x_49);
x_51 = lean_apply_4(x_9, x_46, x_47, x_48, x_50);
return x_51;
}
case 8:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 2);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 3);
lean_inc(x_55);
x_56 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
lean_dec(x_1);
x_57 = lean_box_uint64(x_56);
x_58 = lean_apply_5(x_10, x_52, x_53, x_54, x_55, x_57);
return x_58;
}
case 9:
{
lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_61 = lean_box_uint64(x_60);
x_62 = lean_apply_2(x_11, x_59, x_61);
return x_62;
}
case 10:
{
lean_object* x_63; lean_object* x_64; uint64_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_13);
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
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_66 = lean_box_uint64(x_65);
x_67 = lean_apply_3(x_12, x_63, x_64, x_66);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint64_t x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
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
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 2);
lean_inc(x_70);
x_71 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_72 = lean_box_uint64(x_71);
x_73 = lean_apply_4(x_13, x_68, x_69, x_70, x_72);
return x_73;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3___rarg), 13, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1127____closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_ctorName___closed__10;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
switch (lean_obj_tag(x_8)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
case 1:
{
uint8_t x_15; 
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_7, 0);
lean_dec(x_16);
x_17 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
case 2:
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_dec(x_7);
x_25 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
case 3:
{
uint8_t x_27; 
lean_dec(x_8);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_7, 0);
lean_dec(x_28);
x_29 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
lean_ctor_set(x_7, 0, x_29);
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
case 4:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_7);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_7, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 0);
lean_inc(x_35);
lean_dec(x_8);
x_36 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_37 = l_Lean_Name_append(x_36, x_35);
lean_ctor_set(x_7, 0, x_37);
return x_7;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_dec(x_7);
x_39 = lean_ctor_get(x_8, 0);
lean_inc(x_39);
lean_dec(x_8);
x_40 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_41 = l_Lean_Name_append(x_40, x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
case 5:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
lean_dec(x_8);
x_46 = l_Lean_Expr_getAppFn(x_45);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 4)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_49 = l_Lean_Name_append(x_48, x_47);
lean_ctor_set(x_7, 0, x_49);
return x_7;
}
else
{
lean_object* x_50; 
lean_dec(x_46);
x_50 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
lean_ctor_set(x_7, 0, x_50);
return x_7;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_7, 1);
lean_inc(x_51);
lean_dec(x_7);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
lean_dec(x_8);
x_53 = l_Lean_Expr_getAppFn(x_52);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 4)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_56 = l_Lean_Name_append(x_55, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_53);
x_58 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
case 6:
{
uint8_t x_60; 
lean_dec(x_8);
x_60 = !lean_is_exclusive(x_7);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_7, 0);
lean_dec(x_61);
x_62 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
lean_ctor_set(x_7, 0, x_62);
return x_7;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
case 7:
{
uint8_t x_66; 
lean_dec(x_8);
x_66 = !lean_is_exclusive(x_7);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_7, 0);
lean_dec(x_67);
x_68 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
lean_ctor_set(x_7, 0, x_68);
return x_7;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_7, 1);
lean_inc(x_69);
lean_dec(x_7);
x_70 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
case 8:
{
uint8_t x_72; 
lean_dec(x_8);
x_72 = !lean_is_exclusive(x_7);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_7, 0);
lean_dec(x_73);
x_74 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
lean_ctor_set(x_7, 0, x_74);
return x_7;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_7, 1);
lean_inc(x_75);
lean_dec(x_7);
x_76 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
case 9:
{
uint8_t x_78; 
lean_dec(x_8);
x_78 = !lean_is_exclusive(x_7);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_7, 0);
lean_dec(x_79);
x_80 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
lean_ctor_set(x_7, 0, x_80);
return x_7;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_7, 1);
lean_inc(x_81);
lean_dec(x_7);
x_82 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
case 10:
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_8, 0);
lean_inc(x_84);
lean_dec(x_8);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_7);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_7, 0);
lean_dec(x_86);
x_87 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_ctor_set(x_7, 0, x_87);
return x_7;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_7, 1);
lean_inc(x_88);
lean_dec(x_7);
x_89 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_7);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_7, 0);
lean_dec(x_94);
x_95 = lean_ctor_get(x_91, 0);
lean_inc(x_95);
lean_dec(x_91);
x_96 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_97 = l_Lean_Name_append(x_96, x_95);
lean_ctor_set(x_7, 0, x_97);
return x_7;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_7, 1);
lean_inc(x_98);
lean_dec(x_7);
x_99 = lean_ctor_get(x_91, 0);
lean_inc(x_99);
lean_dec(x_91);
x_100 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_101 = l_Lean_Name_append(x_100, x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_98);
return x_102;
}
}
else
{
uint8_t x_103; 
lean_dec(x_92);
lean_dec(x_91);
x_103 = !lean_is_exclusive(x_7);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_7, 0);
lean_dec(x_104);
x_105 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_ctor_set(x_7, 0, x_105);
return x_7;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
lean_dec(x_7);
x_107 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
}
default: 
{
uint8_t x_109; 
lean_dec(x_8);
x_109 = !lean_is_exclusive(x_7);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_7, 0);
lean_dec(x_110);
x_111 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
lean_ctor_set(x_7, 0, x_111);
return x_7;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_dec(x_7);
x_113 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_getExprKind(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getPPOption_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_8);
x_9 = lean_apply_1(x_1, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_getPPAll(x_8);
lean_dec(x_8);
x_14 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_box(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_17);
x_18 = lean_apply_1(x_1, x_17);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_getPPAll(x_17);
lean_dec(x_17);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
x_23 = 1;
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_7);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
lean_inc(x_32);
x_33 = lean_apply_1(x_1, x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_getPPAll(x_32);
lean_dec(x_32);
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_7);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_32);
x_38 = 1;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
}
}
}
}
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_3);
x_9 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_15;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_3);
x_9 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_14);
return x_15;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_mul(x_11, x_13);
lean_dec(x_11);
x_15 = lean_nat_add(x_14, x_2);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_1);
x_16 = lean_apply_6(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 4);
x_21 = lean_ctor_get(x_4, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_22 = lean_unsigned_to_nat(3u);
x_23 = lean_nat_mul(x_17, x_22);
lean_dec(x_17);
x_24 = lean_nat_add(x_23, x_2);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
x_26 = lean_apply_6(x_3, x_25, x_5, x_6, x_7, x_8, x_9);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_descend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_descend___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Delaborator.Basic");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Delaborator.withAppFn");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3;
x_3 = lean_unsigned_to_nat(191u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
x_16 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4;
x_17 = lean_panic_fn(x_15, x_16);
x_18 = lean_apply_6(x_17, x_2, x_3, x_4, x_5, x_6, x_14);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Delaborator.withAppArg");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1;
x_3 = lean_unsigned_to_nat(195u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
x_16 = l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2;
x_17 = lean_panic_fn(x_15, x_16);
x_18 = lean_apply_6(x_17, x_2, x_3, x_4, x_5, x_6, x_14);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFnArgs___rarg), 8, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_13 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg(x_12, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_apply_1(x_2, x_14);
x_17 = l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg(x_16, x_3, x_4, x_5, x_6, x_7, x_15);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
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
lean_dec(x_2);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_22);
return x_23;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFnArgs___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_bindingDomain_x21(x_9);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingDomain___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1), 8, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Expr_bindingBody_x21(x_1);
x_11 = lean_expr_instantiate1(x_10, x_3);
lean_dec(x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_11, x_12, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_binderInfo(x_10);
x_13 = l_Lean_Expr_bindingDomain_x21(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1___boxed), 9, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_2);
x_15 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg(x_1, x_12, x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 11)
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withProj_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Delaborator.withProj");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1;
x_3 = lean_unsigned_to_nat(215u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 11)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_PrettyPrinter_Delaborator_descend___rarg(x_11, x_12, x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
x_16 = l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2;
x_17 = lean_panic_fn(x_15, x_16);
x_18 = lean_apply_6(x_17, x_2, x_3, x_4, x_5, x_6, x_14);
return x_18;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withProj___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 10)
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.Delaborator.withMDataExpr");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1;
x_3 = lean_unsigned_to_nat(219u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 10)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 0);
lean_dec(x_13);
lean_ctor_set(x_2, 0, x_11);
x_14 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
x_19 = lean_ctor_get(x_2, 5);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_17);
lean_ctor_set(x_20, 4, x_18);
lean_ctor_set(x_20, 5, x_19);
x_21 = lean_apply_6(x_1, x_20, x_3, x_4, x_5, x_6, x_10);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_1);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
x_24 = l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2;
x_25 = lean_panic_fn(x_23, x_24);
x_26 = lean_apply_6(x_25, x_2, x_3, x_4, x_5, x_6, x_22);
return x_26;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 1)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get_usize(x_5, 2);
x_14 = lean_ctor_get(x_5, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_6, 1);
x_17 = lean_ctor_get_usize(x_6, 2);
x_18 = lean_ctor_get(x_6, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_7, 1);
x_21 = lean_ctor_get_usize(x_7, 2);
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_8, 1);
x_25 = lean_ctor_get_usize(x_8, 2);
x_26 = lean_ctor_get(x_8, 0);
lean_dec(x_26);
x_27 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_28 = lean_string_dec_eq(x_24, x_27);
lean_dec(x_24);
if (x_28 == 0)
{
lean_object* x_29; 
lean_free_object(x_8);
lean_free_object(x_7);
lean_dec(x_20);
lean_free_object(x_6);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_29 = lean_apply_1(x_4, x_1);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_31 = lean_string_dec_eq(x_20, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
lean_ctor_set(x_8, 1, x_27);
x_35 = lean_apply_1(x_4, x_1);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
lean_ctor_set(x_8, 1, x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_5);
lean_ctor_set(x_36, 1, x_10);
x_37 = lean_apply_1(x_4, x_36);
return x_37;
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_20);
x_38 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_39 = lean_string_dec_eq(x_16, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 1);
lean_dec(x_41);
x_42 = lean_ctor_get(x_1, 0);
lean_dec(x_42);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_7, 1, x_30);
x_43 = lean_apply_1(x_4, x_1);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_1);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_7, 1, x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_5);
lean_ctor_set(x_44, 1, x_10);
x_45 = lean_apply_1(x_4, x_44);
return x_45;
}
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_16);
x_46 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_47 = lean_string_dec_eq(x_12, x_46);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_1, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 0);
lean_dec(x_50);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_6, 1, x_38);
x_51 = lean_apply_1(x_4, x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_1);
lean_ctor_set(x_8, 1, x_27);
lean_ctor_set(x_7, 1, x_30);
lean_ctor_set(x_6, 1, x_38);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_10);
x_53 = lean_apply_1(x_4, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_8);
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_54 = lean_box_usize(x_25);
x_55 = lean_box_usize(x_21);
x_56 = lean_box_usize(x_17);
x_57 = lean_box_usize(x_13);
x_58 = lean_apply_6(x_3, x_1, x_10, x_54, x_55, x_56, x_57);
return x_58;
}
}
}
}
}
else
{
lean_object* x_59; size_t x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_8, 1);
x_60 = lean_ctor_get_usize(x_8, 2);
lean_inc(x_59);
lean_dec(x_8);
x_61 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_62 = lean_string_dec_eq(x_59, x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_object* x_63; 
lean_free_object(x_7);
lean_dec(x_20);
lean_free_object(x_6);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_63 = lean_apply_1(x_4, x_1);
return x_63;
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_65 = lean_string_dec_eq(x_20, x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_66 = x_1;
} else {
 lean_dec_ref(x_1);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_67, 0, x_9);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set_usize(x_67, 2, x_60);
lean_ctor_set(x_7, 0, x_67);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_5);
lean_ctor_set(x_68, 1, x_10);
x_69 = lean_apply_1(x_4, x_68);
return x_69;
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_20);
x_70 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_71 = lean_string_dec_eq(x_16, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_72 = x_1;
} else {
 lean_dec_ref(x_1);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_73, 0, x_9);
lean_ctor_set(x_73, 1, x_61);
lean_ctor_set_usize(x_73, 2, x_60);
lean_ctor_set(x_7, 1, x_64);
lean_ctor_set(x_7, 0, x_73);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_5);
lean_ctor_set(x_74, 1, x_10);
x_75 = lean_apply_1(x_4, x_74);
return x_75;
}
else
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_16);
x_76 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_77 = lean_string_dec_eq(x_12, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_78 = x_1;
} else {
 lean_dec_ref(x_1);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_79, 0, x_9);
lean_ctor_set(x_79, 1, x_61);
lean_ctor_set_usize(x_79, 2, x_60);
lean_ctor_set(x_7, 1, x_64);
lean_ctor_set(x_7, 0, x_79);
lean_ctor_set(x_6, 1, x_70);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_10);
x_81 = lean_apply_1(x_4, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_7);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_82 = lean_box_usize(x_60);
x_83 = lean_box_usize(x_21);
x_84 = lean_box_usize(x_17);
x_85 = lean_box_usize(x_13);
x_86 = lean_apply_6(x_3, x_1, x_10, x_82, x_83, x_84, x_85);
return x_86;
}
}
}
}
}
}
else
{
lean_object* x_87; size_t x_88; lean_object* x_89; size_t x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_87 = lean_ctor_get(x_7, 1);
x_88 = lean_ctor_get_usize(x_7, 2);
lean_inc(x_87);
lean_dec(x_7);
x_89 = lean_ctor_get(x_8, 1);
lean_inc(x_89);
x_90 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_93 = lean_string_dec_eq(x_89, x_92);
lean_dec(x_89);
if (x_93 == 0)
{
lean_object* x_94; 
lean_dec(x_91);
lean_dec(x_87);
lean_free_object(x_6);
lean_dec(x_16);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_94 = lean_apply_1(x_4, x_1);
return x_94;
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_96 = lean_string_dec_eq(x_87, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_97 = x_1;
} else {
 lean_dec_ref(x_1);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_9);
lean_ctor_set(x_98, 1, x_92);
lean_ctor_set_usize(x_98, 2, x_90);
x_99 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_87);
lean_ctor_set_usize(x_99, 2, x_88);
lean_ctor_set(x_6, 0, x_99);
if (lean_is_scalar(x_97)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_97;
}
lean_ctor_set(x_100, 0, x_5);
lean_ctor_set(x_100, 1, x_10);
x_101 = lean_apply_1(x_4, x_100);
return x_101;
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec(x_87);
x_102 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_103 = lean_string_dec_eq(x_16, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_104 = x_1;
} else {
 lean_dec_ref(x_1);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_105 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_105 = x_91;
}
lean_ctor_set(x_105, 0, x_9);
lean_ctor_set(x_105, 1, x_92);
lean_ctor_set_usize(x_105, 2, x_90);
x_106 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_95);
lean_ctor_set_usize(x_106, 2, x_88);
lean_ctor_set(x_6, 0, x_106);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_5);
lean_ctor_set(x_107, 1, x_10);
x_108 = lean_apply_1(x_4, x_107);
return x_108;
}
else
{
lean_object* x_109; uint8_t x_110; 
lean_dec(x_16);
x_109 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_110 = lean_string_dec_eq(x_12, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_111 = x_1;
} else {
 lean_dec_ref(x_1);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_112 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_112 = x_91;
}
lean_ctor_set(x_112, 0, x_9);
lean_ctor_set(x_112, 1, x_92);
lean_ctor_set_usize(x_112, 2, x_90);
x_113 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_95);
lean_ctor_set_usize(x_113, 2, x_88);
lean_ctor_set(x_6, 1, x_102);
lean_ctor_set(x_6, 0, x_113);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_5);
lean_ctor_set(x_114, 1, x_10);
x_115 = lean_apply_1(x_4, x_114);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_91);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_116 = lean_box_usize(x_90);
x_117 = lean_box_usize(x_88);
x_118 = lean_box_usize(x_17);
x_119 = lean_box_usize(x_13);
x_120 = lean_apply_6(x_3, x_1, x_10, x_116, x_117, x_118, x_119);
return x_120;
}
}
}
}
}
}
else
{
lean_object* x_121; size_t x_122; lean_object* x_123; size_t x_124; lean_object* x_125; lean_object* x_126; size_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_121 = lean_ctor_get(x_6, 1);
x_122 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_121);
lean_dec(x_6);
x_123 = lean_ctor_get(x_7, 1);
lean_inc(x_123);
x_124 = lean_ctor_get_usize(x_7, 2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_125 = x_7;
} else {
 lean_dec_ref(x_7);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_8, 1);
lean_inc(x_126);
x_127 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_128 = x_8;
} else {
 lean_dec_ref(x_8);
 x_128 = lean_box(0);
}
x_129 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_130 = lean_string_dec_eq(x_126, x_129);
lean_dec(x_126);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_121);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_3);
x_131 = lean_apply_1(x_4, x_1);
return x_131;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_133 = lean_string_dec_eq(x_123, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_134 = x_1;
} else {
 lean_dec_ref(x_1);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_135 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_135 = x_128;
}
lean_ctor_set(x_135, 0, x_9);
lean_ctor_set(x_135, 1, x_129);
lean_ctor_set_usize(x_135, 2, x_127);
if (lean_is_scalar(x_125)) {
 x_136 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_136 = x_125;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_123);
lean_ctor_set_usize(x_136, 2, x_124);
x_137 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_121);
lean_ctor_set_usize(x_137, 2, x_122);
lean_ctor_set(x_5, 0, x_137);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_5);
lean_ctor_set(x_138, 1, x_10);
x_139 = lean_apply_1(x_4, x_138);
return x_139;
}
else
{
lean_object* x_140; uint8_t x_141; 
lean_dec(x_123);
x_140 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_141 = lean_string_dec_eq(x_121, x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_142 = x_1;
} else {
 lean_dec_ref(x_1);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_9);
lean_ctor_set(x_143, 1, x_129);
lean_ctor_set_usize(x_143, 2, x_127);
if (lean_is_scalar(x_125)) {
 x_144 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_144 = x_125;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_132);
lean_ctor_set_usize(x_144, 2, x_124);
x_145 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_121);
lean_ctor_set_usize(x_145, 2, x_122);
lean_ctor_set(x_5, 0, x_145);
if (lean_is_scalar(x_142)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_142;
}
lean_ctor_set(x_146, 0, x_5);
lean_ctor_set(x_146, 1, x_10);
x_147 = lean_apply_1(x_4, x_146);
return x_147;
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_121);
x_148 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_149 = lean_string_dec_eq(x_12, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_150 = x_1;
} else {
 lean_dec_ref(x_1);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_151 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_151 = x_128;
}
lean_ctor_set(x_151, 0, x_9);
lean_ctor_set(x_151, 1, x_129);
lean_ctor_set_usize(x_151, 2, x_127);
if (lean_is_scalar(x_125)) {
 x_152 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_152 = x_125;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_132);
lean_ctor_set_usize(x_152, 2, x_124);
x_153 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_140);
lean_ctor_set_usize(x_153, 2, x_122);
lean_ctor_set(x_5, 0, x_153);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_5);
lean_ctor_set(x_154, 1, x_10);
x_155 = lean_apply_1(x_4, x_154);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_128);
lean_dec(x_125);
lean_free_object(x_5);
lean_dec(x_12);
lean_dec(x_4);
x_156 = lean_box_usize(x_127);
x_157 = lean_box_usize(x_124);
x_158 = lean_box_usize(x_122);
x_159 = lean_box_usize(x_13);
x_160 = lean_apply_6(x_3, x_1, x_10, x_156, x_157, x_158, x_159);
return x_160;
}
}
}
}
}
}
else
{
lean_object* x_161; size_t x_162; lean_object* x_163; size_t x_164; lean_object* x_165; lean_object* x_166; size_t x_167; lean_object* x_168; lean_object* x_169; size_t x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_161 = lean_ctor_get(x_5, 1);
x_162 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_161);
lean_dec(x_5);
x_163 = lean_ctor_get(x_6, 1);
lean_inc(x_163);
x_164 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_165 = x_6;
} else {
 lean_dec_ref(x_6);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_7, 1);
lean_inc(x_166);
x_167 = lean_ctor_get_usize(x_7, 2);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_168 = x_7;
} else {
 lean_dec_ref(x_7);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_8, 1);
lean_inc(x_169);
x_170 = lean_ctor_get_usize(x_8, 2);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_171 = x_8;
} else {
 lean_dec_ref(x_8);
 x_171 = lean_box(0);
}
x_172 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_173 = lean_string_dec_eq(x_169, x_172);
lean_dec(x_169);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_10);
lean_dec(x_3);
x_174 = lean_apply_1(x_4, x_1);
return x_174;
}
else
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_176 = lean_string_dec_eq(x_166, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_177 = x_1;
} else {
 lean_dec_ref(x_1);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_178 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_178 = x_171;
}
lean_ctor_set(x_178, 0, x_9);
lean_ctor_set(x_178, 1, x_172);
lean_ctor_set_usize(x_178, 2, x_170);
if (lean_is_scalar(x_168)) {
 x_179 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_179 = x_168;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_166);
lean_ctor_set_usize(x_179, 2, x_167);
if (lean_is_scalar(x_165)) {
 x_180 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_180 = x_165;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_163);
lean_ctor_set_usize(x_180, 2, x_164);
x_181 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_161);
lean_ctor_set_usize(x_181, 2, x_162);
if (lean_is_scalar(x_177)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_177;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_10);
x_183 = lean_apply_1(x_4, x_182);
return x_183;
}
else
{
lean_object* x_184; uint8_t x_185; 
lean_dec(x_166);
x_184 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_185 = lean_string_dec_eq(x_163, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_186 = x_1;
} else {
 lean_dec_ref(x_1);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_187 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_187 = x_171;
}
lean_ctor_set(x_187, 0, x_9);
lean_ctor_set(x_187, 1, x_172);
lean_ctor_set_usize(x_187, 2, x_170);
if (lean_is_scalar(x_168)) {
 x_188 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_188 = x_168;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_175);
lean_ctor_set_usize(x_188, 2, x_167);
if (lean_is_scalar(x_165)) {
 x_189 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_189 = x_165;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_163);
lean_ctor_set_usize(x_189, 2, x_164);
x_190 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_161);
lean_ctor_set_usize(x_190, 2, x_162);
if (lean_is_scalar(x_186)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_186;
}
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_10);
x_192 = lean_apply_1(x_4, x_191);
return x_192;
}
else
{
lean_object* x_193; uint8_t x_194; 
lean_dec(x_163);
x_193 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_194 = lean_string_dec_eq(x_161, x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_195 = x_1;
} else {
 lean_dec_ref(x_1);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_196 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_196 = x_171;
}
lean_ctor_set(x_196, 0, x_9);
lean_ctor_set(x_196, 1, x_172);
lean_ctor_set_usize(x_196, 2, x_170);
if (lean_is_scalar(x_168)) {
 x_197 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_197 = x_168;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_175);
lean_ctor_set_usize(x_197, 2, x_167);
if (lean_is_scalar(x_165)) {
 x_198 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_198 = x_165;
}
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_184);
lean_ctor_set_usize(x_198, 2, x_164);
x_199 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_161);
lean_ctor_set_usize(x_199, 2, x_162);
if (lean_is_scalar(x_195)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_195;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_10);
x_201 = lean_apply_1(x_4, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_165);
lean_dec(x_161);
lean_dec(x_4);
x_202 = lean_box_usize(x_170);
x_203 = lean_box_usize(x_167);
x_204 = lean_box_usize(x_164);
x_205 = lean_box_usize(x_162);
x_206 = lean_apply_6(x_3, x_1, x_10, x_202, x_203, x_204, x_205);
return x_206;
}
}
}
}
}
}
else
{
lean_object* x_207; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_207 = lean_apply_1(x_4, x_1);
return x_207;
}
}
else
{
lean_object* x_208; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_208 = lean_apply_1(x_4, x_1);
return x_208;
}
}
else
{
lean_object* x_209; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_209 = lean_apply_1(x_4, x_1);
return x_209;
}
}
else
{
lean_object* x_210; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_210 = lean_apply_1(x_4, x_1);
return x_210;
}
}
else
{
lean_object* x_211; 
lean_dec(x_5);
lean_dec(x_3);
x_211 = lean_apply_1(x_4, x_1);
return x_211;
}
}
case 3:
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_4);
lean_dec(x_3);
x_212 = lean_ctor_get(x_1, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_1, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_1, 2);
lean_inc(x_214);
x_215 = lean_ctor_get(x_1, 3);
lean_inc(x_215);
x_216 = lean_apply_5(x_2, x_1, x_212, x_213, x_214, x_215);
return x_216;
}
default: 
{
lean_object* x_217; 
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_apply_1(x_4, x_1);
return x_217;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_isAtom___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get_usize(x_3, 2);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_5, 1);
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_6, 1);
x_19 = lean_ctor_get(x_6, 0);
lean_dec(x_19);
x_20 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_21 = lean_string_dec_eq(x_18, x_20);
lean_dec(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_9);
x_22 = l_Lean_Syntax_getArgs(x_2);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Array_findIdx_x3f_loop___rarg(x_22, x_24, x_23, x_25, lean_box(0));
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_2);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_box(0);
lean_ctor_set(x_26, 0, x_1);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_32);
x_34 = lean_array_get_size(x_8);
x_35 = lean_nat_dec_lt(x_31, x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_31);
return x_2;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_array_fget(x_8, x_31);
x_37 = lean_box(0);
x_38 = lean_array_fset(x_8, x_31, x_37);
x_39 = l_Lean_Syntax_setInfo(x_33, x_36);
x_40 = lean_array_fset(x_38, x_31, x_39);
lean_dec(x_31);
lean_ctor_set(x_2, 1, x_40);
return x_2;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_44, 2, x_42);
x_45 = lean_array_get_size(x_8);
x_46 = lean_nat_dec_lt(x_41, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_41);
return x_2;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_array_fget(x_8, x_41);
x_48 = lean_box(0);
x_49 = lean_array_fset(x_8, x_41, x_48);
x_50 = l_Lean_Syntax_setInfo(x_44, x_47);
x_51 = lean_array_fset(x_49, x_41, x_50);
lean_dec(x_41);
lean_ctor_set(x_2, 1, x_51);
return x_2;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_2);
x_52 = lean_ctor_get(x_26, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_53 = x_26;
} else {
 lean_dec_ref(x_26);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(1, 1, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_1);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_54);
x_57 = lean_array_get_size(x_8);
x_58 = lean_nat_dec_lt(x_52, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_dec(x_52);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_8);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_array_fget(x_8, x_52);
x_61 = lean_box(0);
x_62 = lean_array_fset(x_8, x_52, x_61);
x_63 = l_Lean_Syntax_setInfo(x_56, x_60);
x_64 = lean_array_fset(x_62, x_52, x_63);
lean_dec(x_52);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_3);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_2);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_2, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_2, 0);
lean_dec(x_68);
x_69 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_70 = lean_string_dec_eq(x_15, x_69);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_3, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_3, 0);
lean_dec(x_73);
lean_ctor_set(x_6, 1, x_20);
lean_inc(x_8);
lean_inc(x_3);
x_74 = l_Lean_Syntax_getArgs(x_2);
x_75 = lean_array_get_size(x_74);
x_76 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Array_findIdx_x3f_loop___rarg(x_74, x_76, x_75, x_77, lean_box(0));
lean_dec(x_74);
if (lean_obj_tag(x_78) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_79; 
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_box(0);
lean_ctor_set(x_78, 0, x_1);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_81);
x_83 = lean_array_get_size(x_8);
x_84 = lean_nat_dec_lt(x_80, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_80);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_3);
lean_ctor_set(x_85, 1, x_8);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_array_fget(x_8, x_80);
x_87 = lean_box(0);
x_88 = lean_array_fset(x_8, x_80, x_87);
x_89 = l_Lean_Syntax_setInfo(x_82, x_86);
x_90 = lean_array_fset(x_88, x_80, x_89);
lean_dec(x_80);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_3);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_92 = lean_ctor_get(x_78, 0);
lean_inc(x_92);
lean_dec(x_78);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_1);
x_95 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_95, 2, x_93);
x_96 = lean_array_get_size(x_8);
x_97 = lean_nat_dec_lt(x_92, x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_3);
lean_ctor_set(x_98, 1, x_8);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_array_fget(x_8, x_92);
x_100 = lean_box(0);
x_101 = lean_array_fset(x_8, x_92, x_100);
x_102 = l_Lean_Syntax_setInfo(x_95, x_99);
x_103 = lean_array_fset(x_101, x_92, x_102);
lean_dec(x_92);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_3);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
x_105 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_105, 0, x_4);
lean_ctor_set(x_105, 1, x_9);
lean_ctor_set_usize(x_105, 2, x_11);
lean_inc(x_8);
lean_inc(x_105);
lean_ctor_set(x_2, 0, x_105);
x_106 = l_Lean_Syntax_getArgs(x_2);
x_107 = lean_array_get_size(x_106);
x_108 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Array_findIdx_x3f_loop___rarg(x_106, x_108, x_107, x_109, lean_box(0));
lean_dec(x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_dec(x_105);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_2);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 x_112 = x_110;
} else {
 lean_dec_ref(x_110);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(1, 1, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_1);
x_115 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
lean_ctor_set(x_115, 2, x_113);
x_116 = lean_array_get_size(x_8);
x_117 = lean_nat_dec_lt(x_111, x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_105);
lean_ctor_set(x_118, 1, x_8);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_array_fget(x_8, x_111);
x_120 = lean_box(0);
x_121 = lean_array_fset(x_8, x_111, x_120);
x_122 = l_Lean_Syntax_setInfo(x_115, x_119);
x_123 = lean_array_fset(x_121, x_111, x_122);
lean_dec(x_111);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_105);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
lean_object* x_125; uint8_t x_126; 
lean_dec(x_15);
x_125 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_126 = lean_string_dec_eq(x_12, x_125);
if (x_126 == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_3);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_3, 1);
lean_dec(x_128);
x_129 = lean_ctor_get(x_3, 0);
lean_dec(x_129);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_69);
lean_inc(x_8);
lean_inc(x_3);
x_130 = l_Lean_Syntax_getArgs(x_2);
x_131 = lean_array_get_size(x_130);
x_132 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_133 = lean_unsigned_to_nat(0u);
x_134 = l_Array_findIdx_x3f_loop___rarg(x_130, x_132, x_131, x_133, lean_box(0));
lean_dec(x_130);
if (lean_obj_tag(x_134) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_135; 
lean_dec(x_2);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = lean_box(0);
lean_ctor_set(x_134, 0, x_1);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_134);
lean_ctor_set(x_138, 2, x_137);
x_139 = lean_array_get_size(x_8);
x_140 = lean_nat_dec_lt(x_136, x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_dec(x_138);
lean_dec(x_136);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_3);
lean_ctor_set(x_141, 1, x_8);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_array_fget(x_8, x_136);
x_143 = lean_box(0);
x_144 = lean_array_fset(x_8, x_136, x_143);
x_145 = l_Lean_Syntax_setInfo(x_138, x_142);
x_146 = lean_array_fset(x_144, x_136, x_145);
lean_dec(x_136);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_3);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_148 = lean_ctor_get(x_134, 0);
lean_inc(x_148);
lean_dec(x_134);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_1);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
lean_ctor_set(x_151, 2, x_149);
x_152 = lean_array_get_size(x_8);
x_153 = lean_nat_dec_lt(x_148, x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; 
lean_dec(x_151);
lean_dec(x_148);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_3);
lean_ctor_set(x_154, 1, x_8);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_array_fget(x_8, x_148);
x_156 = lean_box(0);
x_157 = lean_array_fset(x_8, x_148, x_156);
x_158 = l_Lean_Syntax_setInfo(x_151, x_155);
x_159 = lean_array_fset(x_157, x_148, x_158);
lean_dec(x_148);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_3);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_69);
x_161 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_9);
lean_ctor_set_usize(x_161, 2, x_11);
lean_inc(x_8);
lean_inc(x_161);
lean_ctor_set(x_2, 0, x_161);
x_162 = l_Lean_Syntax_getArgs(x_2);
x_163 = lean_array_get_size(x_162);
x_164 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_165 = lean_unsigned_to_nat(0u);
x_166 = l_Array_findIdx_x3f_loop___rarg(x_162, x_164, x_163, x_165, lean_box(0));
lean_dec(x_162);
if (lean_obj_tag(x_166) == 0)
{
lean_dec(x_161);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_2);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
x_169 = lean_box(0);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_168;
}
lean_ctor_set(x_170, 0, x_1);
x_171 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
lean_ctor_set(x_171, 2, x_169);
x_172 = lean_array_get_size(x_8);
x_173 = lean_nat_dec_lt(x_167, x_172);
lean_dec(x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_171);
lean_dec(x_167);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_161);
lean_ctor_set(x_174, 1, x_8);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_array_fget(x_8, x_167);
x_176 = lean_box(0);
x_177 = lean_array_fset(x_8, x_167, x_176);
x_178 = l_Lean_Syntax_setInfo(x_171, x_175);
x_179 = lean_array_fset(x_177, x_167, x_178);
lean_dec(x_167);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_161);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_181; uint8_t x_182; 
lean_dec(x_12);
x_181 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_182 = lean_string_dec_eq(x_9, x_181);
if (x_182 == 0)
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_3);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_3, 1);
lean_dec(x_184);
x_185 = lean_ctor_get(x_3, 0);
lean_dec(x_185);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_69);
lean_ctor_set(x_4, 1, x_125);
lean_inc(x_8);
lean_inc(x_3);
x_186 = l_Lean_Syntax_getArgs(x_2);
x_187 = lean_array_get_size(x_186);
x_188 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_189 = lean_unsigned_to_nat(0u);
x_190 = l_Array_findIdx_x3f_loop___rarg(x_186, x_188, x_187, x_189, lean_box(0));
lean_dec(x_186);
if (lean_obj_tag(x_190) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_191; 
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_box(0);
lean_ctor_set(x_190, 0, x_1);
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_190);
lean_ctor_set(x_194, 2, x_193);
x_195 = lean_array_get_size(x_8);
x_196 = lean_nat_dec_lt(x_192, x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_194);
lean_dec(x_192);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_3);
lean_ctor_set(x_197, 1, x_8);
return x_197;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_198 = lean_array_fget(x_8, x_192);
x_199 = lean_box(0);
x_200 = lean_array_fset(x_8, x_192, x_199);
x_201 = l_Lean_Syntax_setInfo(x_194, x_198);
x_202 = lean_array_fset(x_200, x_192, x_201);
lean_dec(x_192);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_3);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_204 = lean_ctor_get(x_190, 0);
lean_inc(x_204);
lean_dec(x_190);
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_206, 0, x_1);
x_207 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
lean_ctor_set(x_207, 2, x_205);
x_208 = lean_array_get_size(x_8);
x_209 = lean_nat_dec_lt(x_204, x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_207);
lean_dec(x_204);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_3);
lean_ctor_set(x_210, 1, x_8);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_array_fget(x_8, x_204);
x_212 = lean_box(0);
x_213 = lean_array_fset(x_8, x_204, x_212);
x_214 = l_Lean_Syntax_setInfo(x_207, x_211);
x_215 = lean_array_fset(x_213, x_204, x_214);
lean_dec(x_204);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_3);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_69);
lean_ctor_set(x_4, 1, x_125);
x_217 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_217, 0, x_4);
lean_ctor_set(x_217, 1, x_9);
lean_ctor_set_usize(x_217, 2, x_11);
lean_inc(x_8);
lean_inc(x_217);
lean_ctor_set(x_2, 0, x_217);
x_218 = l_Lean_Syntax_getArgs(x_2);
x_219 = lean_array_get_size(x_218);
x_220 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_221 = lean_unsigned_to_nat(0u);
x_222 = l_Array_findIdx_x3f_loop___rarg(x_218, x_220, x_219, x_221, lean_box(0));
lean_dec(x_218);
if (lean_obj_tag(x_222) == 0)
{
lean_dec(x_217);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
lean_dec(x_2);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_224 = x_222;
} else {
 lean_dec_ref(x_222);
 x_224 = lean_box(0);
}
x_225 = lean_box(0);
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_1);
x_227 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set(x_227, 2, x_225);
x_228 = lean_array_get_size(x_8);
x_229 = lean_nat_dec_lt(x_223, x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
lean_dec(x_227);
lean_dec(x_223);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_217);
lean_ctor_set(x_230, 1, x_8);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_231 = lean_array_fget(x_8, x_223);
x_232 = lean_box(0);
x_233 = lean_array_fset(x_8, x_223, x_232);
x_234 = l_Lean_Syntax_setInfo(x_227, x_231);
x_235 = lean_array_fset(x_233, x_223, x_234);
lean_dec(x_223);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_217);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_237 = lean_array_get_size(x_8);
x_238 = lean_unsigned_to_nat(0u);
x_239 = lean_nat_dec_lt(x_238, x_237);
lean_dec(x_237);
if (x_239 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_240 = lean_array_fget(x_8, x_238);
x_241 = lean_box(0);
x_242 = lean_array_fset(x_8, x_238, x_241);
x_243 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_240);
x_244 = lean_array_fset(x_242, x_238, x_243);
lean_ctor_set(x_2, 1, x_244);
return x_2;
}
}
}
}
}
else
{
lean_object* x_245; uint8_t x_246; 
lean_dec(x_2);
x_245 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_246 = lean_string_dec_eq(x_15, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_247 = x_3;
} else {
 lean_dec_ref(x_3);
 x_247 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_4);
lean_ctor_set(x_248, 1, x_9);
lean_ctor_set_usize(x_248, 2, x_11);
lean_inc(x_8);
lean_inc(x_248);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_8);
x_250 = l_Lean_Syntax_getArgs(x_249);
x_251 = lean_array_get_size(x_250);
x_252 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_253 = lean_unsigned_to_nat(0u);
x_254 = l_Array_findIdx_x3f_loop___rarg(x_250, x_252, x_251, x_253, lean_box(0));
lean_dec(x_250);
if (lean_obj_tag(x_254) == 0)
{
lean_dec(x_248);
lean_dec(x_8);
lean_dec(x_1);
return x_249;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
lean_dec(x_249);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_box(0);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(1, 1, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_1);
x_259 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
lean_ctor_set(x_259, 2, x_257);
x_260 = lean_array_get_size(x_8);
x_261 = lean_nat_dec_lt(x_255, x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec(x_259);
lean_dec(x_255);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_248);
lean_ctor_set(x_262, 1, x_8);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_array_fget(x_8, x_255);
x_264 = lean_box(0);
x_265 = lean_array_fset(x_8, x_255, x_264);
x_266 = l_Lean_Syntax_setInfo(x_259, x_263);
x_267 = lean_array_fset(x_265, x_255, x_266);
lean_dec(x_255);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_248);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; uint8_t x_270; 
lean_dec(x_15);
x_269 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_270 = lean_string_dec_eq(x_12, x_269);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_271 = x_3;
} else {
 lean_dec_ref(x_3);
 x_271 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_245);
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_4);
lean_ctor_set(x_272, 1, x_9);
lean_ctor_set_usize(x_272, 2, x_11);
lean_inc(x_8);
lean_inc(x_272);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_8);
x_274 = l_Lean_Syntax_getArgs(x_273);
x_275 = lean_array_get_size(x_274);
x_276 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_277 = lean_unsigned_to_nat(0u);
x_278 = l_Array_findIdx_x3f_loop___rarg(x_274, x_276, x_275, x_277, lean_box(0));
lean_dec(x_274);
if (lean_obj_tag(x_278) == 0)
{
lean_dec(x_272);
lean_dec(x_8);
lean_dec(x_1);
return x_273;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
lean_dec(x_273);
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_278)) {
 lean_ctor_release(x_278, 0);
 x_280 = x_278;
} else {
 lean_dec_ref(x_278);
 x_280 = lean_box(0);
}
x_281 = lean_box(0);
if (lean_is_scalar(x_280)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_280;
}
lean_ctor_set(x_282, 0, x_1);
x_283 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_283, 0, x_281);
lean_ctor_set(x_283, 1, x_282);
lean_ctor_set(x_283, 2, x_281);
x_284 = lean_array_get_size(x_8);
x_285 = lean_nat_dec_lt(x_279, x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_object* x_286; 
lean_dec(x_283);
lean_dec(x_279);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_272);
lean_ctor_set(x_286, 1, x_8);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_287 = lean_array_fget(x_8, x_279);
x_288 = lean_box(0);
x_289 = lean_array_fset(x_8, x_279, x_288);
x_290 = l_Lean_Syntax_setInfo(x_283, x_287);
x_291 = lean_array_fset(x_289, x_279, x_290);
lean_dec(x_279);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_272);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
lean_object* x_293; uint8_t x_294; 
lean_dec(x_12);
x_293 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_294 = lean_string_dec_eq(x_9, x_293);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_295 = x_3;
} else {
 lean_dec_ref(x_3);
 x_295 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_245);
lean_ctor_set(x_4, 1, x_269);
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_4);
lean_ctor_set(x_296, 1, x_9);
lean_ctor_set_usize(x_296, 2, x_11);
lean_inc(x_8);
lean_inc(x_296);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_296);
lean_ctor_set(x_297, 1, x_8);
x_298 = l_Lean_Syntax_getArgs(x_297);
x_299 = lean_array_get_size(x_298);
x_300 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_301 = lean_unsigned_to_nat(0u);
x_302 = l_Array_findIdx_x3f_loop___rarg(x_298, x_300, x_299, x_301, lean_box(0));
lean_dec(x_298);
if (lean_obj_tag(x_302) == 0)
{
lean_dec(x_296);
lean_dec(x_8);
lean_dec(x_1);
return x_297;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_dec(x_297);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_304 = x_302;
} else {
 lean_dec_ref(x_302);
 x_304 = lean_box(0);
}
x_305 = lean_box(0);
if (lean_is_scalar(x_304)) {
 x_306 = lean_alloc_ctor(1, 1, 0);
} else {
 x_306 = x_304;
}
lean_ctor_set(x_306, 0, x_1);
x_307 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
lean_ctor_set(x_307, 2, x_305);
x_308 = lean_array_get_size(x_8);
x_309 = lean_nat_dec_lt(x_303, x_308);
lean_dec(x_308);
if (x_309 == 0)
{
lean_object* x_310; 
lean_dec(x_307);
lean_dec(x_303);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_296);
lean_ctor_set(x_310, 1, x_8);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_311 = lean_array_fget(x_8, x_303);
x_312 = lean_box(0);
x_313 = lean_array_fset(x_8, x_303, x_312);
x_314 = l_Lean_Syntax_setInfo(x_307, x_311);
x_315 = lean_array_fset(x_313, x_303, x_314);
lean_dec(x_303);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_296);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; uint8_t x_319; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_317 = lean_array_get_size(x_8);
x_318 = lean_unsigned_to_nat(0u);
x_319 = lean_nat_dec_lt(x_318, x_317);
lean_dec(x_317);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_1);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_3);
lean_ctor_set(x_320, 1, x_8);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_321 = lean_array_fget(x_8, x_318);
x_322 = lean_box(0);
x_323 = lean_array_fset(x_8, x_318, x_322);
x_324 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_321);
x_325 = lean_array_fset(x_323, x_318, x_324);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_3);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
}
}
}
else
{
lean_object* x_327; size_t x_328; lean_object* x_329; uint8_t x_330; 
x_327 = lean_ctor_get(x_6, 1);
x_328 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_327);
lean_dec(x_6);
x_329 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_330 = lean_string_dec_eq(x_327, x_329);
lean_dec(x_327);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_free_object(x_5);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_9);
x_331 = l_Lean_Syntax_getArgs(x_2);
x_332 = lean_array_get_size(x_331);
x_333 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_334 = lean_unsigned_to_nat(0u);
x_335 = l_Array_findIdx_x3f_loop___rarg(x_331, x_333, x_332, x_334, lean_box(0));
lean_dec(x_331);
if (lean_obj_tag(x_335) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_336 = x_2;
} else {
 lean_dec_ref(x_2);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_335, 0);
lean_inc(x_337);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_338 = x_335;
} else {
 lean_dec_ref(x_335);
 x_338 = lean_box(0);
}
x_339 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_340 = lean_alloc_ctor(1, 1, 0);
} else {
 x_340 = x_338;
}
lean_ctor_set(x_340, 0, x_1);
x_341 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
lean_ctor_set(x_341, 2, x_339);
x_342 = lean_array_get_size(x_8);
x_343 = lean_nat_dec_lt(x_337, x_342);
lean_dec(x_342);
if (x_343 == 0)
{
lean_object* x_344; 
lean_dec(x_341);
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_336;
}
lean_ctor_set(x_344, 0, x_3);
lean_ctor_set(x_344, 1, x_8);
return x_344;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_345 = lean_array_fget(x_8, x_337);
x_346 = lean_box(0);
x_347 = lean_array_fset(x_8, x_337, x_346);
x_348 = l_Lean_Syntax_setInfo(x_341, x_345);
x_349 = lean_array_fset(x_347, x_337, x_348);
lean_dec(x_337);
if (lean_is_scalar(x_336)) {
 x_350 = lean_alloc_ctor(1, 2, 0);
} else {
 x_350 = x_336;
}
lean_ctor_set(x_350, 0, x_3);
lean_ctor_set(x_350, 1, x_349);
return x_350;
}
}
}
else
{
lean_object* x_351; lean_object* x_352; uint8_t x_353; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_351 = x_2;
} else {
 lean_dec_ref(x_2);
 x_351 = lean_box(0);
}
x_352 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_353 = lean_string_dec_eq(x_15, x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_354 = x_3;
} else {
 lean_dec_ref(x_3);
 x_354 = lean_box(0);
}
x_355 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_355, 0, x_7);
lean_ctor_set(x_355, 1, x_329);
lean_ctor_set_usize(x_355, 2, x_328);
lean_ctor_set(x_5, 0, x_355);
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_4);
lean_ctor_set(x_356, 1, x_9);
lean_ctor_set_usize(x_356, 2, x_11);
lean_inc(x_8);
lean_inc(x_356);
if (lean_is_scalar(x_351)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_351;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_8);
x_358 = l_Lean_Syntax_getArgs(x_357);
x_359 = lean_array_get_size(x_358);
x_360 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_361 = lean_unsigned_to_nat(0u);
x_362 = l_Array_findIdx_x3f_loop___rarg(x_358, x_360, x_359, x_361, lean_box(0));
lean_dec(x_358);
if (lean_obj_tag(x_362) == 0)
{
lean_dec(x_356);
lean_dec(x_8);
lean_dec(x_1);
return x_357;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
lean_dec(x_357);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
x_365 = lean_box(0);
if (lean_is_scalar(x_364)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_364;
}
lean_ctor_set(x_366, 0, x_1);
x_367 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
lean_ctor_set(x_367, 2, x_365);
x_368 = lean_array_get_size(x_8);
x_369 = lean_nat_dec_lt(x_363, x_368);
lean_dec(x_368);
if (x_369 == 0)
{
lean_object* x_370; 
lean_dec(x_367);
lean_dec(x_363);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_356);
lean_ctor_set(x_370, 1, x_8);
return x_370;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_371 = lean_array_fget(x_8, x_363);
x_372 = lean_box(0);
x_373 = lean_array_fset(x_8, x_363, x_372);
x_374 = l_Lean_Syntax_setInfo(x_367, x_371);
x_375 = lean_array_fset(x_373, x_363, x_374);
lean_dec(x_363);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_356);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
lean_object* x_377; uint8_t x_378; 
lean_dec(x_15);
x_377 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_378 = lean_string_dec_eq(x_12, x_377);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_379 = x_3;
} else {
 lean_dec_ref(x_3);
 x_379 = lean_box(0);
}
x_380 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_380, 0, x_7);
lean_ctor_set(x_380, 1, x_329);
lean_ctor_set_usize(x_380, 2, x_328);
lean_ctor_set(x_5, 1, x_352);
lean_ctor_set(x_5, 0, x_380);
if (lean_is_scalar(x_379)) {
 x_381 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_381 = x_379;
}
lean_ctor_set(x_381, 0, x_4);
lean_ctor_set(x_381, 1, x_9);
lean_ctor_set_usize(x_381, 2, x_11);
lean_inc(x_8);
lean_inc(x_381);
if (lean_is_scalar(x_351)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_351;
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_8);
x_383 = l_Lean_Syntax_getArgs(x_382);
x_384 = lean_array_get_size(x_383);
x_385 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_386 = lean_unsigned_to_nat(0u);
x_387 = l_Array_findIdx_x3f_loop___rarg(x_383, x_385, x_384, x_386, lean_box(0));
lean_dec(x_383);
if (lean_obj_tag(x_387) == 0)
{
lean_dec(x_381);
lean_dec(x_8);
lean_dec(x_1);
return x_382;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; 
lean_dec(x_382);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_389 = x_387;
} else {
 lean_dec_ref(x_387);
 x_389 = lean_box(0);
}
x_390 = lean_box(0);
if (lean_is_scalar(x_389)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_389;
}
lean_ctor_set(x_391, 0, x_1);
x_392 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
lean_ctor_set(x_392, 2, x_390);
x_393 = lean_array_get_size(x_8);
x_394 = lean_nat_dec_lt(x_388, x_393);
lean_dec(x_393);
if (x_394 == 0)
{
lean_object* x_395; 
lean_dec(x_392);
lean_dec(x_388);
x_395 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_395, 0, x_381);
lean_ctor_set(x_395, 1, x_8);
return x_395;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = lean_array_fget(x_8, x_388);
x_397 = lean_box(0);
x_398 = lean_array_fset(x_8, x_388, x_397);
x_399 = l_Lean_Syntax_setInfo(x_392, x_396);
x_400 = lean_array_fset(x_398, x_388, x_399);
lean_dec(x_388);
x_401 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_401, 0, x_381);
lean_ctor_set(x_401, 1, x_400);
return x_401;
}
}
}
else
{
lean_object* x_402; uint8_t x_403; 
lean_dec(x_12);
x_402 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_403 = lean_string_dec_eq(x_9, x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_404 = x_3;
} else {
 lean_dec_ref(x_3);
 x_404 = lean_box(0);
}
x_405 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_405, 0, x_7);
lean_ctor_set(x_405, 1, x_329);
lean_ctor_set_usize(x_405, 2, x_328);
lean_ctor_set(x_5, 1, x_352);
lean_ctor_set(x_5, 0, x_405);
lean_ctor_set(x_4, 1, x_377);
if (lean_is_scalar(x_404)) {
 x_406 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_406 = x_404;
}
lean_ctor_set(x_406, 0, x_4);
lean_ctor_set(x_406, 1, x_9);
lean_ctor_set_usize(x_406, 2, x_11);
lean_inc(x_8);
lean_inc(x_406);
if (lean_is_scalar(x_351)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_351;
}
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_8);
x_408 = l_Lean_Syntax_getArgs(x_407);
x_409 = lean_array_get_size(x_408);
x_410 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_411 = lean_unsigned_to_nat(0u);
x_412 = l_Array_findIdx_x3f_loop___rarg(x_408, x_410, x_409, x_411, lean_box(0));
lean_dec(x_408);
if (lean_obj_tag(x_412) == 0)
{
lean_dec(x_406);
lean_dec(x_8);
lean_dec(x_1);
return x_407;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
lean_dec(x_407);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 x_414 = x_412;
} else {
 lean_dec_ref(x_412);
 x_414 = lean_box(0);
}
x_415 = lean_box(0);
if (lean_is_scalar(x_414)) {
 x_416 = lean_alloc_ctor(1, 1, 0);
} else {
 x_416 = x_414;
}
lean_ctor_set(x_416, 0, x_1);
x_417 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set(x_417, 2, x_415);
x_418 = lean_array_get_size(x_8);
x_419 = lean_nat_dec_lt(x_413, x_418);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; 
lean_dec(x_417);
lean_dec(x_413);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_406);
lean_ctor_set(x_420, 1, x_8);
return x_420;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_421 = lean_array_fget(x_8, x_413);
x_422 = lean_box(0);
x_423 = lean_array_fset(x_8, x_413, x_422);
x_424 = l_Lean_Syntax_setInfo(x_417, x_421);
x_425 = lean_array_fset(x_423, x_413, x_424);
lean_dec(x_413);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_406);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
else
{
lean_object* x_427; lean_object* x_428; uint8_t x_429; 
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_427 = lean_array_get_size(x_8);
x_428 = lean_unsigned_to_nat(0u);
x_429 = lean_nat_dec_lt(x_428, x_427);
lean_dec(x_427);
if (x_429 == 0)
{
lean_object* x_430; 
lean_dec(x_1);
if (lean_is_scalar(x_351)) {
 x_430 = lean_alloc_ctor(1, 2, 0);
} else {
 x_430 = x_351;
}
lean_ctor_set(x_430, 0, x_3);
lean_ctor_set(x_430, 1, x_8);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_431 = lean_array_fget(x_8, x_428);
x_432 = lean_box(0);
x_433 = lean_array_fset(x_8, x_428, x_432);
x_434 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_431);
x_435 = lean_array_fset(x_433, x_428, x_434);
if (lean_is_scalar(x_351)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_351;
}
lean_ctor_set(x_436, 0, x_3);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
}
}
}
}
else
{
lean_object* x_437; size_t x_438; lean_object* x_439; size_t x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_437 = lean_ctor_get(x_5, 1);
x_438 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_437);
lean_dec(x_5);
x_439 = lean_ctor_get(x_6, 1);
lean_inc(x_439);
x_440 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_441 = x_6;
} else {
 lean_dec_ref(x_6);
 x_441 = lean_box(0);
}
x_442 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_443 = lean_string_dec_eq(x_439, x_442);
lean_dec(x_439);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_441);
lean_dec(x_437);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_9);
x_444 = l_Lean_Syntax_getArgs(x_2);
x_445 = lean_array_get_size(x_444);
x_446 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_447 = lean_unsigned_to_nat(0u);
x_448 = l_Array_findIdx_x3f_loop___rarg(x_444, x_446, x_445, x_447, lean_box(0));
lean_dec(x_444);
if (lean_obj_tag(x_448) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_449 = x_2;
} else {
 lean_dec_ref(x_2);
 x_449 = lean_box(0);
}
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
if (lean_is_exclusive(x_448)) {
 lean_ctor_release(x_448, 0);
 x_451 = x_448;
} else {
 lean_dec_ref(x_448);
 x_451 = lean_box(0);
}
x_452 = lean_box(0);
if (lean_is_scalar(x_451)) {
 x_453 = lean_alloc_ctor(1, 1, 0);
} else {
 x_453 = x_451;
}
lean_ctor_set(x_453, 0, x_1);
x_454 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_453);
lean_ctor_set(x_454, 2, x_452);
x_455 = lean_array_get_size(x_8);
x_456 = lean_nat_dec_lt(x_450, x_455);
lean_dec(x_455);
if (x_456 == 0)
{
lean_object* x_457; 
lean_dec(x_454);
lean_dec(x_450);
if (lean_is_scalar(x_449)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_449;
}
lean_ctor_set(x_457, 0, x_3);
lean_ctor_set(x_457, 1, x_8);
return x_457;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_458 = lean_array_fget(x_8, x_450);
x_459 = lean_box(0);
x_460 = lean_array_fset(x_8, x_450, x_459);
x_461 = l_Lean_Syntax_setInfo(x_454, x_458);
x_462 = lean_array_fset(x_460, x_450, x_461);
lean_dec(x_450);
if (lean_is_scalar(x_449)) {
 x_463 = lean_alloc_ctor(1, 2, 0);
} else {
 x_463 = x_449;
}
lean_ctor_set(x_463, 0, x_3);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
else
{
lean_object* x_464; lean_object* x_465; uint8_t x_466; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_464 = x_2;
} else {
 lean_dec_ref(x_2);
 x_464 = lean_box(0);
}
x_465 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_466 = lean_string_dec_eq(x_437, x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_467 = x_3;
} else {
 lean_dec_ref(x_3);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_468 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_468 = x_441;
}
lean_ctor_set(x_468, 0, x_7);
lean_ctor_set(x_468, 1, x_442);
lean_ctor_set_usize(x_468, 2, x_440);
x_469 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_437);
lean_ctor_set_usize(x_469, 2, x_438);
lean_ctor_set(x_4, 0, x_469);
if (lean_is_scalar(x_467)) {
 x_470 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_470 = x_467;
}
lean_ctor_set(x_470, 0, x_4);
lean_ctor_set(x_470, 1, x_9);
lean_ctor_set_usize(x_470, 2, x_11);
lean_inc(x_8);
lean_inc(x_470);
if (lean_is_scalar(x_464)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_464;
}
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_8);
x_472 = l_Lean_Syntax_getArgs(x_471);
x_473 = lean_array_get_size(x_472);
x_474 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_475 = lean_unsigned_to_nat(0u);
x_476 = l_Array_findIdx_x3f_loop___rarg(x_472, x_474, x_473, x_475, lean_box(0));
lean_dec(x_472);
if (lean_obj_tag(x_476) == 0)
{
lean_dec(x_470);
lean_dec(x_8);
lean_dec(x_1);
return x_471;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; 
lean_dec(x_471);
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_478 = x_476;
} else {
 lean_dec_ref(x_476);
 x_478 = lean_box(0);
}
x_479 = lean_box(0);
if (lean_is_scalar(x_478)) {
 x_480 = lean_alloc_ctor(1, 1, 0);
} else {
 x_480 = x_478;
}
lean_ctor_set(x_480, 0, x_1);
x_481 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
lean_ctor_set(x_481, 2, x_479);
x_482 = lean_array_get_size(x_8);
x_483 = lean_nat_dec_lt(x_477, x_482);
lean_dec(x_482);
if (x_483 == 0)
{
lean_object* x_484; 
lean_dec(x_481);
lean_dec(x_477);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_470);
lean_ctor_set(x_484, 1, x_8);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_485 = lean_array_fget(x_8, x_477);
x_486 = lean_box(0);
x_487 = lean_array_fset(x_8, x_477, x_486);
x_488 = l_Lean_Syntax_setInfo(x_481, x_485);
x_489 = lean_array_fset(x_487, x_477, x_488);
lean_dec(x_477);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_470);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
else
{
lean_object* x_491; uint8_t x_492; 
lean_dec(x_437);
x_491 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_492 = lean_string_dec_eq(x_12, x_491);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_493 = x_3;
} else {
 lean_dec_ref(x_3);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_494 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_494 = x_441;
}
lean_ctor_set(x_494, 0, x_7);
lean_ctor_set(x_494, 1, x_442);
lean_ctor_set_usize(x_494, 2, x_440);
x_495 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_465);
lean_ctor_set_usize(x_495, 2, x_438);
lean_ctor_set(x_4, 0, x_495);
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_496 = x_493;
}
lean_ctor_set(x_496, 0, x_4);
lean_ctor_set(x_496, 1, x_9);
lean_ctor_set_usize(x_496, 2, x_11);
lean_inc(x_8);
lean_inc(x_496);
if (lean_is_scalar(x_464)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_464;
}
lean_ctor_set(x_497, 0, x_496);
lean_ctor_set(x_497, 1, x_8);
x_498 = l_Lean_Syntax_getArgs(x_497);
x_499 = lean_array_get_size(x_498);
x_500 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_501 = lean_unsigned_to_nat(0u);
x_502 = l_Array_findIdx_x3f_loop___rarg(x_498, x_500, x_499, x_501, lean_box(0));
lean_dec(x_498);
if (lean_obj_tag(x_502) == 0)
{
lean_dec(x_496);
lean_dec(x_8);
lean_dec(x_1);
return x_497;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; 
lean_dec(x_497);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 x_504 = x_502;
} else {
 lean_dec_ref(x_502);
 x_504 = lean_box(0);
}
x_505 = lean_box(0);
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(1, 1, 0);
} else {
 x_506 = x_504;
}
lean_ctor_set(x_506, 0, x_1);
x_507 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_507, 0, x_505);
lean_ctor_set(x_507, 1, x_506);
lean_ctor_set(x_507, 2, x_505);
x_508 = lean_array_get_size(x_8);
x_509 = lean_nat_dec_lt(x_503, x_508);
lean_dec(x_508);
if (x_509 == 0)
{
lean_object* x_510; 
lean_dec(x_507);
lean_dec(x_503);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_496);
lean_ctor_set(x_510, 1, x_8);
return x_510;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_511 = lean_array_fget(x_8, x_503);
x_512 = lean_box(0);
x_513 = lean_array_fset(x_8, x_503, x_512);
x_514 = l_Lean_Syntax_setInfo(x_507, x_511);
x_515 = lean_array_fset(x_513, x_503, x_514);
lean_dec(x_503);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_496);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
lean_object* x_517; uint8_t x_518; 
lean_dec(x_12);
x_517 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_518 = lean_string_dec_eq(x_9, x_517);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_519 = x_3;
} else {
 lean_dec_ref(x_3);
 x_519 = lean_box(0);
}
if (lean_is_scalar(x_441)) {
 x_520 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_520 = x_441;
}
lean_ctor_set(x_520, 0, x_7);
lean_ctor_set(x_520, 1, x_442);
lean_ctor_set_usize(x_520, 2, x_440);
x_521 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_465);
lean_ctor_set_usize(x_521, 2, x_438);
lean_ctor_set(x_4, 1, x_491);
lean_ctor_set(x_4, 0, x_521);
if (lean_is_scalar(x_519)) {
 x_522 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_522 = x_519;
}
lean_ctor_set(x_522, 0, x_4);
lean_ctor_set(x_522, 1, x_9);
lean_ctor_set_usize(x_522, 2, x_11);
lean_inc(x_8);
lean_inc(x_522);
if (lean_is_scalar(x_464)) {
 x_523 = lean_alloc_ctor(1, 2, 0);
} else {
 x_523 = x_464;
}
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_8);
x_524 = l_Lean_Syntax_getArgs(x_523);
x_525 = lean_array_get_size(x_524);
x_526 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_527 = lean_unsigned_to_nat(0u);
x_528 = l_Array_findIdx_x3f_loop___rarg(x_524, x_526, x_525, x_527, lean_box(0));
lean_dec(x_524);
if (lean_obj_tag(x_528) == 0)
{
lean_dec(x_522);
lean_dec(x_8);
lean_dec(x_1);
return x_523;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
lean_dec(x_523);
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
if (lean_is_exclusive(x_528)) {
 lean_ctor_release(x_528, 0);
 x_530 = x_528;
} else {
 lean_dec_ref(x_528);
 x_530 = lean_box(0);
}
x_531 = lean_box(0);
if (lean_is_scalar(x_530)) {
 x_532 = lean_alloc_ctor(1, 1, 0);
} else {
 x_532 = x_530;
}
lean_ctor_set(x_532, 0, x_1);
x_533 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
lean_ctor_set(x_533, 2, x_531);
x_534 = lean_array_get_size(x_8);
x_535 = lean_nat_dec_lt(x_529, x_534);
lean_dec(x_534);
if (x_535 == 0)
{
lean_object* x_536; 
lean_dec(x_533);
lean_dec(x_529);
x_536 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_536, 0, x_522);
lean_ctor_set(x_536, 1, x_8);
return x_536;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_537 = lean_array_fget(x_8, x_529);
x_538 = lean_box(0);
x_539 = lean_array_fset(x_8, x_529, x_538);
x_540 = l_Lean_Syntax_setInfo(x_533, x_537);
x_541 = lean_array_fset(x_539, x_529, x_540);
lean_dec(x_529);
x_542 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_542, 0, x_522);
lean_ctor_set(x_542, 1, x_541);
return x_542;
}
}
}
else
{
lean_object* x_543; lean_object* x_544; uint8_t x_545; 
lean_dec(x_441);
lean_free_object(x_4);
lean_dec(x_9);
x_543 = lean_array_get_size(x_8);
x_544 = lean_unsigned_to_nat(0u);
x_545 = lean_nat_dec_lt(x_544, x_543);
lean_dec(x_543);
if (x_545 == 0)
{
lean_object* x_546; 
lean_dec(x_1);
if (lean_is_scalar(x_464)) {
 x_546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_546 = x_464;
}
lean_ctor_set(x_546, 0, x_3);
lean_ctor_set(x_546, 1, x_8);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_547 = lean_array_fget(x_8, x_544);
x_548 = lean_box(0);
x_549 = lean_array_fset(x_8, x_544, x_548);
x_550 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_547);
x_551 = lean_array_fset(x_549, x_544, x_550);
if (lean_is_scalar(x_464)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_464;
}
lean_ctor_set(x_552, 0, x_3);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
}
}
}
}
else
{
size_t x_553; lean_object* x_554; size_t x_555; lean_object* x_556; size_t x_557; lean_object* x_558; lean_object* x_559; size_t x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_553 = lean_ctor_get_usize(x_3, 2);
x_554 = lean_ctor_get(x_4, 1);
x_555 = lean_ctor_get_usize(x_4, 2);
lean_inc(x_554);
lean_dec(x_4);
x_556 = lean_ctor_get(x_5, 1);
lean_inc(x_556);
x_557 = lean_ctor_get_usize(x_5, 2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_558 = x_5;
} else {
 lean_dec_ref(x_5);
 x_558 = lean_box(0);
}
x_559 = lean_ctor_get(x_6, 1);
lean_inc(x_559);
x_560 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_561 = x_6;
} else {
 lean_dec_ref(x_6);
 x_561 = lean_box(0);
}
x_562 = l_myMacro____x40_Init_Notation___hyg_340____closed__1;
x_563 = lean_string_dec_eq(x_559, x_562);
lean_dec(x_559);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_556);
lean_dec(x_554);
lean_dec(x_9);
x_564 = l_Lean_Syntax_getArgs(x_2);
x_565 = lean_array_get_size(x_564);
x_566 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_567 = lean_unsigned_to_nat(0u);
x_568 = l_Array_findIdx_x3f_loop___rarg(x_564, x_566, x_565, x_567, lean_box(0));
lean_dec(x_564);
if (lean_obj_tag(x_568) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_569 = x_2;
} else {
 lean_dec_ref(x_2);
 x_569 = lean_box(0);
}
x_570 = lean_ctor_get(x_568, 0);
lean_inc(x_570);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 x_571 = x_568;
} else {
 lean_dec_ref(x_568);
 x_571 = lean_box(0);
}
x_572 = lean_box(0);
if (lean_is_scalar(x_571)) {
 x_573 = lean_alloc_ctor(1, 1, 0);
} else {
 x_573 = x_571;
}
lean_ctor_set(x_573, 0, x_1);
x_574 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
lean_ctor_set(x_574, 2, x_572);
x_575 = lean_array_get_size(x_8);
x_576 = lean_nat_dec_lt(x_570, x_575);
lean_dec(x_575);
if (x_576 == 0)
{
lean_object* x_577; 
lean_dec(x_574);
lean_dec(x_570);
if (lean_is_scalar(x_569)) {
 x_577 = lean_alloc_ctor(1, 2, 0);
} else {
 x_577 = x_569;
}
lean_ctor_set(x_577, 0, x_3);
lean_ctor_set(x_577, 1, x_8);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_578 = lean_array_fget(x_8, x_570);
x_579 = lean_box(0);
x_580 = lean_array_fset(x_8, x_570, x_579);
x_581 = l_Lean_Syntax_setInfo(x_574, x_578);
x_582 = lean_array_fset(x_580, x_570, x_581);
lean_dec(x_570);
if (lean_is_scalar(x_569)) {
 x_583 = lean_alloc_ctor(1, 2, 0);
} else {
 x_583 = x_569;
}
lean_ctor_set(x_583, 0, x_3);
lean_ctor_set(x_583, 1, x_582);
return x_583;
}
}
}
else
{
lean_object* x_584; lean_object* x_585; uint8_t x_586; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_584 = x_2;
} else {
 lean_dec_ref(x_2);
 x_584 = lean_box(0);
}
x_585 = l_myMacro____x40_Init_Notation___hyg_340____closed__3;
x_586 = lean_string_dec_eq(x_556, x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_587 = x_3;
} else {
 lean_dec_ref(x_3);
 x_587 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_588 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_588 = x_561;
}
lean_ctor_set(x_588, 0, x_7);
lean_ctor_set(x_588, 1, x_562);
lean_ctor_set_usize(x_588, 2, x_560);
if (lean_is_scalar(x_558)) {
 x_589 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_589 = x_558;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_556);
lean_ctor_set_usize(x_589, 2, x_557);
x_590 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_554);
lean_ctor_set_usize(x_590, 2, x_555);
if (lean_is_scalar(x_587)) {
 x_591 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_591 = x_587;
}
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_9);
lean_ctor_set_usize(x_591, 2, x_553);
lean_inc(x_8);
lean_inc(x_591);
if (lean_is_scalar(x_584)) {
 x_592 = lean_alloc_ctor(1, 2, 0);
} else {
 x_592 = x_584;
}
lean_ctor_set(x_592, 0, x_591);
lean_ctor_set(x_592, 1, x_8);
x_593 = l_Lean_Syntax_getArgs(x_592);
x_594 = lean_array_get_size(x_593);
x_595 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_596 = lean_unsigned_to_nat(0u);
x_597 = l_Array_findIdx_x3f_loop___rarg(x_593, x_595, x_594, x_596, lean_box(0));
lean_dec(x_593);
if (lean_obj_tag(x_597) == 0)
{
lean_dec(x_591);
lean_dec(x_8);
lean_dec(x_1);
return x_592;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
lean_dec(x_592);
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
if (lean_is_exclusive(x_597)) {
 lean_ctor_release(x_597, 0);
 x_599 = x_597;
} else {
 lean_dec_ref(x_597);
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
x_603 = lean_array_get_size(x_8);
x_604 = lean_nat_dec_lt(x_598, x_603);
lean_dec(x_603);
if (x_604 == 0)
{
lean_object* x_605; 
lean_dec(x_602);
lean_dec(x_598);
x_605 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_605, 0, x_591);
lean_ctor_set(x_605, 1, x_8);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_606 = lean_array_fget(x_8, x_598);
x_607 = lean_box(0);
x_608 = lean_array_fset(x_8, x_598, x_607);
x_609 = l_Lean_Syntax_setInfo(x_602, x_606);
x_610 = lean_array_fset(x_608, x_598, x_609);
lean_dec(x_598);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_591);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
else
{
lean_object* x_612; uint8_t x_613; 
lean_dec(x_556);
x_612 = l_myMacro____x40_Init_Notation___hyg_1916____closed__1;
x_613 = lean_string_dec_eq(x_554, x_612);
if (x_613 == 0)
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_614 = x_3;
} else {
 lean_dec_ref(x_3);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_615 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_615 = x_561;
}
lean_ctor_set(x_615, 0, x_7);
lean_ctor_set(x_615, 1, x_562);
lean_ctor_set_usize(x_615, 2, x_560);
if (lean_is_scalar(x_558)) {
 x_616 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_616 = x_558;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_585);
lean_ctor_set_usize(x_616, 2, x_557);
x_617 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_554);
lean_ctor_set_usize(x_617, 2, x_555);
if (lean_is_scalar(x_614)) {
 x_618 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_618 = x_614;
}
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_9);
lean_ctor_set_usize(x_618, 2, x_553);
lean_inc(x_8);
lean_inc(x_618);
if (lean_is_scalar(x_584)) {
 x_619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_619 = x_584;
}
lean_ctor_set(x_619, 0, x_618);
lean_ctor_set(x_619, 1, x_8);
x_620 = l_Lean_Syntax_getArgs(x_619);
x_621 = lean_array_get_size(x_620);
x_622 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_623 = lean_unsigned_to_nat(0u);
x_624 = l_Array_findIdx_x3f_loop___rarg(x_620, x_622, x_621, x_623, lean_box(0));
lean_dec(x_620);
if (lean_obj_tag(x_624) == 0)
{
lean_dec(x_618);
lean_dec(x_8);
lean_dec(x_1);
return x_619;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
lean_dec(x_619);
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
if (lean_is_exclusive(x_624)) {
 lean_ctor_release(x_624, 0);
 x_626 = x_624;
} else {
 lean_dec_ref(x_624);
 x_626 = lean_box(0);
}
x_627 = lean_box(0);
if (lean_is_scalar(x_626)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_626;
}
lean_ctor_set(x_628, 0, x_1);
x_629 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
lean_ctor_set(x_629, 2, x_627);
x_630 = lean_array_get_size(x_8);
x_631 = lean_nat_dec_lt(x_625, x_630);
lean_dec(x_630);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_629);
lean_dec(x_625);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_618);
lean_ctor_set(x_632, 1, x_8);
return x_632;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_633 = lean_array_fget(x_8, x_625);
x_634 = lean_box(0);
x_635 = lean_array_fset(x_8, x_625, x_634);
x_636 = l_Lean_Syntax_setInfo(x_629, x_633);
x_637 = lean_array_fset(x_635, x_625, x_636);
lean_dec(x_625);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_618);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
else
{
lean_object* x_639; uint8_t x_640; 
lean_dec(x_554);
x_639 = l_myMacro____x40_Init_Notation___hyg_1916____closed__3;
x_640 = lean_string_dec_eq(x_9, x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_641 = x_3;
} else {
 lean_dec_ref(x_3);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_642 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_642 = x_561;
}
lean_ctor_set(x_642, 0, x_7);
lean_ctor_set(x_642, 1, x_562);
lean_ctor_set_usize(x_642, 2, x_560);
if (lean_is_scalar(x_558)) {
 x_643 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_643 = x_558;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_585);
lean_ctor_set_usize(x_643, 2, x_557);
x_644 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_612);
lean_ctor_set_usize(x_644, 2, x_555);
if (lean_is_scalar(x_641)) {
 x_645 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_645 = x_641;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_9);
lean_ctor_set_usize(x_645, 2, x_553);
lean_inc(x_8);
lean_inc(x_645);
if (lean_is_scalar(x_584)) {
 x_646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_646 = x_584;
}
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_8);
x_647 = l_Lean_Syntax_getArgs(x_646);
x_648 = lean_array_get_size(x_647);
x_649 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_650 = lean_unsigned_to_nat(0u);
x_651 = l_Array_findIdx_x3f_loop___rarg(x_647, x_649, x_648, x_650, lean_box(0));
lean_dec(x_647);
if (lean_obj_tag(x_651) == 0)
{
lean_dec(x_645);
lean_dec(x_8);
lean_dec(x_1);
return x_646;
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; 
lean_dec(x_646);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 x_653 = x_651;
} else {
 lean_dec_ref(x_651);
 x_653 = lean_box(0);
}
x_654 = lean_box(0);
if (lean_is_scalar(x_653)) {
 x_655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_655 = x_653;
}
lean_ctor_set(x_655, 0, x_1);
x_656 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
lean_ctor_set(x_656, 2, x_654);
x_657 = lean_array_get_size(x_8);
x_658 = lean_nat_dec_lt(x_652, x_657);
lean_dec(x_657);
if (x_658 == 0)
{
lean_object* x_659; 
lean_dec(x_656);
lean_dec(x_652);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_645);
lean_ctor_set(x_659, 1, x_8);
return x_659;
}
else
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_660 = lean_array_fget(x_8, x_652);
x_661 = lean_box(0);
x_662 = lean_array_fset(x_8, x_652, x_661);
x_663 = l_Lean_Syntax_setInfo(x_656, x_660);
x_664 = lean_array_fset(x_662, x_652, x_663);
lean_dec(x_652);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_645);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
else
{
lean_object* x_666; lean_object* x_667; uint8_t x_668; 
lean_dec(x_561);
lean_dec(x_558);
lean_dec(x_9);
x_666 = lean_array_get_size(x_8);
x_667 = lean_unsigned_to_nat(0u);
x_668 = lean_nat_dec_lt(x_667, x_666);
lean_dec(x_666);
if (x_668 == 0)
{
lean_object* x_669; 
lean_dec(x_1);
if (lean_is_scalar(x_584)) {
 x_669 = lean_alloc_ctor(1, 2, 0);
} else {
 x_669 = x_584;
}
lean_ctor_set(x_669, 0, x_3);
lean_ctor_set(x_669, 1, x_8);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_670 = lean_array_fget(x_8, x_667);
x_671 = lean_box(0);
x_672 = lean_array_fset(x_8, x_667, x_671);
x_673 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_670);
x_674 = lean_array_fset(x_672, x_667, x_673);
if (lean_is_scalar(x_584)) {
 x_675 = lean_alloc_ctor(1, 2, 0);
} else {
 x_675 = x_584;
}
lean_ctor_set(x_675, 0, x_3);
lean_ctor_set(x_675, 1, x_674);
return x_675;
}
}
}
}
}
}
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_676 = lean_ctor_get(x_2, 1);
lean_inc(x_676);
x_677 = l_Lean_Syntax_getArgs(x_2);
x_678 = lean_array_get_size(x_677);
x_679 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_680 = lean_unsigned_to_nat(0u);
x_681 = l_Array_findIdx_x3f_loop___rarg(x_677, x_679, x_678, x_680, lean_box(0));
lean_dec(x_677);
if (lean_obj_tag(x_681) == 0)
{
lean_dec(x_676);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_682; 
x_682 = !lean_is_exclusive(x_2);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; uint8_t x_685; 
x_683 = lean_ctor_get(x_2, 1);
lean_dec(x_683);
x_684 = lean_ctor_get(x_2, 0);
lean_dec(x_684);
x_685 = !lean_is_exclusive(x_681);
if (x_685 == 0)
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; uint8_t x_690; 
x_686 = lean_ctor_get(x_681, 0);
x_687 = lean_box(0);
lean_ctor_set(x_681, 0, x_1);
x_688 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_688, 0, x_687);
lean_ctor_set(x_688, 1, x_681);
lean_ctor_set(x_688, 2, x_687);
x_689 = lean_array_get_size(x_676);
x_690 = lean_nat_dec_lt(x_686, x_689);
lean_dec(x_689);
if (x_690 == 0)
{
lean_dec(x_688);
lean_dec(x_686);
return x_2;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_691 = lean_array_fget(x_676, x_686);
x_692 = lean_box(0);
x_693 = lean_array_fset(x_676, x_686, x_692);
x_694 = l_Lean_Syntax_setInfo(x_688, x_691);
x_695 = lean_array_fset(x_693, x_686, x_694);
lean_dec(x_686);
lean_ctor_set(x_2, 1, x_695);
return x_2;
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; uint8_t x_701; 
x_696 = lean_ctor_get(x_681, 0);
lean_inc(x_696);
lean_dec(x_681);
x_697 = lean_box(0);
x_698 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_698, 0, x_1);
x_699 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
lean_ctor_set(x_699, 2, x_697);
x_700 = lean_array_get_size(x_676);
x_701 = lean_nat_dec_lt(x_696, x_700);
lean_dec(x_700);
if (x_701 == 0)
{
lean_dec(x_699);
lean_dec(x_696);
return x_2;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_702 = lean_array_fget(x_676, x_696);
x_703 = lean_box(0);
x_704 = lean_array_fset(x_676, x_696, x_703);
x_705 = l_Lean_Syntax_setInfo(x_699, x_702);
x_706 = lean_array_fset(x_704, x_696, x_705);
lean_dec(x_696);
lean_ctor_set(x_2, 1, x_706);
return x_2;
}
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; 
lean_dec(x_2);
x_707 = lean_ctor_get(x_681, 0);
lean_inc(x_707);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 x_708 = x_681;
} else {
 lean_dec_ref(x_681);
 x_708 = lean_box(0);
}
x_709 = lean_box(0);
if (lean_is_scalar(x_708)) {
 x_710 = lean_alloc_ctor(1, 1, 0);
} else {
 x_710 = x_708;
}
lean_ctor_set(x_710, 0, x_1);
x_711 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
lean_ctor_set(x_711, 2, x_709);
x_712 = lean_array_get_size(x_676);
x_713 = lean_nat_dec_lt(x_707, x_712);
lean_dec(x_712);
if (x_713 == 0)
{
lean_object* x_714; 
lean_dec(x_711);
lean_dec(x_707);
x_714 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_714, 0, x_3);
lean_ctor_set(x_714, 1, x_676);
return x_714;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_715 = lean_array_fget(x_676, x_707);
x_716 = lean_box(0);
x_717 = lean_array_fset(x_676, x_707, x_716);
x_718 = l_Lean_Syntax_setInfo(x_711, x_715);
x_719 = lean_array_fset(x_717, x_707, x_718);
lean_dec(x_707);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_3);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_721 = lean_ctor_get(x_2, 1);
lean_inc(x_721);
x_722 = l_Lean_Syntax_getArgs(x_2);
x_723 = lean_array_get_size(x_722);
x_724 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_725 = lean_unsigned_to_nat(0u);
x_726 = l_Array_findIdx_x3f_loop___rarg(x_722, x_724, x_723, x_725, lean_box(0));
lean_dec(x_722);
if (lean_obj_tag(x_726) == 0)
{
lean_dec(x_721);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_727; 
x_727 = !lean_is_exclusive(x_2);
if (x_727 == 0)
{
lean_object* x_728; lean_object* x_729; uint8_t x_730; 
x_728 = lean_ctor_get(x_2, 1);
lean_dec(x_728);
x_729 = lean_ctor_get(x_2, 0);
lean_dec(x_729);
x_730 = !lean_is_exclusive(x_726);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; 
x_731 = lean_ctor_get(x_726, 0);
x_732 = lean_box(0);
lean_ctor_set(x_726, 0, x_1);
x_733 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_726);
lean_ctor_set(x_733, 2, x_732);
x_734 = lean_array_get_size(x_721);
x_735 = lean_nat_dec_lt(x_731, x_734);
lean_dec(x_734);
if (x_735 == 0)
{
lean_dec(x_733);
lean_dec(x_731);
return x_2;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_736 = lean_array_fget(x_721, x_731);
x_737 = lean_box(0);
x_738 = lean_array_fset(x_721, x_731, x_737);
x_739 = l_Lean_Syntax_setInfo(x_733, x_736);
x_740 = lean_array_fset(x_738, x_731, x_739);
lean_dec(x_731);
lean_ctor_set(x_2, 1, x_740);
return x_2;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; uint8_t x_746; 
x_741 = lean_ctor_get(x_726, 0);
lean_inc(x_741);
lean_dec(x_726);
x_742 = lean_box(0);
x_743 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_743, 0, x_1);
x_744 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_744, 0, x_742);
lean_ctor_set(x_744, 1, x_743);
lean_ctor_set(x_744, 2, x_742);
x_745 = lean_array_get_size(x_721);
x_746 = lean_nat_dec_lt(x_741, x_745);
lean_dec(x_745);
if (x_746 == 0)
{
lean_dec(x_744);
lean_dec(x_741);
return x_2;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_747 = lean_array_fget(x_721, x_741);
x_748 = lean_box(0);
x_749 = lean_array_fset(x_721, x_741, x_748);
x_750 = l_Lean_Syntax_setInfo(x_744, x_747);
x_751 = lean_array_fset(x_749, x_741, x_750);
lean_dec(x_741);
lean_ctor_set(x_2, 1, x_751);
return x_2;
}
}
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; 
lean_dec(x_2);
x_752 = lean_ctor_get(x_726, 0);
lean_inc(x_752);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 x_753 = x_726;
} else {
 lean_dec_ref(x_726);
 x_753 = lean_box(0);
}
x_754 = lean_box(0);
if (lean_is_scalar(x_753)) {
 x_755 = lean_alloc_ctor(1, 1, 0);
} else {
 x_755 = x_753;
}
lean_ctor_set(x_755, 0, x_1);
x_756 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
lean_ctor_set(x_756, 2, x_754);
x_757 = lean_array_get_size(x_721);
x_758 = lean_nat_dec_lt(x_752, x_757);
lean_dec(x_757);
if (x_758 == 0)
{
lean_object* x_759; 
lean_dec(x_756);
lean_dec(x_752);
x_759 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_759, 0, x_3);
lean_ctor_set(x_759, 1, x_721);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_760 = lean_array_fget(x_721, x_752);
x_761 = lean_box(0);
x_762 = lean_array_fset(x_721, x_752, x_761);
x_763 = l_Lean_Syntax_setInfo(x_756, x_760);
x_764 = lean_array_fset(x_762, x_752, x_763);
lean_dec(x_752);
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_3);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_5);
lean_dec(x_4);
x_766 = lean_ctor_get(x_2, 1);
lean_inc(x_766);
x_767 = l_Lean_Syntax_getArgs(x_2);
x_768 = lean_array_get_size(x_767);
x_769 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_770 = lean_unsigned_to_nat(0u);
x_771 = l_Array_findIdx_x3f_loop___rarg(x_767, x_769, x_768, x_770, lean_box(0));
lean_dec(x_767);
if (lean_obj_tag(x_771) == 0)
{
lean_dec(x_766);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_772; 
x_772 = !lean_is_exclusive(x_2);
if (x_772 == 0)
{
lean_object* x_773; lean_object* x_774; uint8_t x_775; 
x_773 = lean_ctor_get(x_2, 1);
lean_dec(x_773);
x_774 = lean_ctor_get(x_2, 0);
lean_dec(x_774);
x_775 = !lean_is_exclusive(x_771);
if (x_775 == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
x_776 = lean_ctor_get(x_771, 0);
x_777 = lean_box(0);
lean_ctor_set(x_771, 0, x_1);
x_778 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_771);
lean_ctor_set(x_778, 2, x_777);
x_779 = lean_array_get_size(x_766);
x_780 = lean_nat_dec_lt(x_776, x_779);
lean_dec(x_779);
if (x_780 == 0)
{
lean_dec(x_778);
lean_dec(x_776);
return x_2;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_781 = lean_array_fget(x_766, x_776);
x_782 = lean_box(0);
x_783 = lean_array_fset(x_766, x_776, x_782);
x_784 = l_Lean_Syntax_setInfo(x_778, x_781);
x_785 = lean_array_fset(x_783, x_776, x_784);
lean_dec(x_776);
lean_ctor_set(x_2, 1, x_785);
return x_2;
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; uint8_t x_791; 
x_786 = lean_ctor_get(x_771, 0);
lean_inc(x_786);
lean_dec(x_771);
x_787 = lean_box(0);
x_788 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_788, 0, x_1);
x_789 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
lean_ctor_set(x_789, 2, x_787);
x_790 = lean_array_get_size(x_766);
x_791 = lean_nat_dec_lt(x_786, x_790);
lean_dec(x_790);
if (x_791 == 0)
{
lean_dec(x_789);
lean_dec(x_786);
return x_2;
}
else
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_792 = lean_array_fget(x_766, x_786);
x_793 = lean_box(0);
x_794 = lean_array_fset(x_766, x_786, x_793);
x_795 = l_Lean_Syntax_setInfo(x_789, x_792);
x_796 = lean_array_fset(x_794, x_786, x_795);
lean_dec(x_786);
lean_ctor_set(x_2, 1, x_796);
return x_2;
}
}
}
else
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; uint8_t x_803; 
lean_dec(x_2);
x_797 = lean_ctor_get(x_771, 0);
lean_inc(x_797);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 x_798 = x_771;
} else {
 lean_dec_ref(x_771);
 x_798 = lean_box(0);
}
x_799 = lean_box(0);
if (lean_is_scalar(x_798)) {
 x_800 = lean_alloc_ctor(1, 1, 0);
} else {
 x_800 = x_798;
}
lean_ctor_set(x_800, 0, x_1);
x_801 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
lean_ctor_set(x_801, 2, x_799);
x_802 = lean_array_get_size(x_766);
x_803 = lean_nat_dec_lt(x_797, x_802);
lean_dec(x_802);
if (x_803 == 0)
{
lean_object* x_804; 
lean_dec(x_801);
lean_dec(x_797);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_3);
lean_ctor_set(x_804, 1, x_766);
return x_804;
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_805 = lean_array_fget(x_766, x_797);
x_806 = lean_box(0);
x_807 = lean_array_fset(x_766, x_797, x_806);
x_808 = l_Lean_Syntax_setInfo(x_801, x_805);
x_809 = lean_array_fset(x_807, x_797, x_808);
lean_dec(x_797);
x_810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_810, 0, x_3);
lean_ctor_set(x_810, 1, x_809);
return x_810;
}
}
}
}
}
else
{
lean_object* x_811; lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_4);
x_811 = lean_ctor_get(x_2, 1);
lean_inc(x_811);
x_812 = l_Lean_Syntax_getArgs(x_2);
x_813 = lean_array_get_size(x_812);
x_814 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_815 = lean_unsigned_to_nat(0u);
x_816 = l_Array_findIdx_x3f_loop___rarg(x_812, x_814, x_813, x_815, lean_box(0));
lean_dec(x_812);
if (lean_obj_tag(x_816) == 0)
{
lean_dec(x_811);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_817; 
x_817 = !lean_is_exclusive(x_2);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; uint8_t x_820; 
x_818 = lean_ctor_get(x_2, 1);
lean_dec(x_818);
x_819 = lean_ctor_get(x_2, 0);
lean_dec(x_819);
x_820 = !lean_is_exclusive(x_816);
if (x_820 == 0)
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; uint8_t x_825; 
x_821 = lean_ctor_get(x_816, 0);
x_822 = lean_box(0);
lean_ctor_set(x_816, 0, x_1);
x_823 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_816);
lean_ctor_set(x_823, 2, x_822);
x_824 = lean_array_get_size(x_811);
x_825 = lean_nat_dec_lt(x_821, x_824);
lean_dec(x_824);
if (x_825 == 0)
{
lean_dec(x_823);
lean_dec(x_821);
return x_2;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_826 = lean_array_fget(x_811, x_821);
x_827 = lean_box(0);
x_828 = lean_array_fset(x_811, x_821, x_827);
x_829 = l_Lean_Syntax_setInfo(x_823, x_826);
x_830 = lean_array_fset(x_828, x_821, x_829);
lean_dec(x_821);
lean_ctor_set(x_2, 1, x_830);
return x_2;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
x_831 = lean_ctor_get(x_816, 0);
lean_inc(x_831);
lean_dec(x_816);
x_832 = lean_box(0);
x_833 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_833, 0, x_1);
x_834 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_834, 0, x_832);
lean_ctor_set(x_834, 1, x_833);
lean_ctor_set(x_834, 2, x_832);
x_835 = lean_array_get_size(x_811);
x_836 = lean_nat_dec_lt(x_831, x_835);
lean_dec(x_835);
if (x_836 == 0)
{
lean_dec(x_834);
lean_dec(x_831);
return x_2;
}
else
{
lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_837 = lean_array_fget(x_811, x_831);
x_838 = lean_box(0);
x_839 = lean_array_fset(x_811, x_831, x_838);
x_840 = l_Lean_Syntax_setInfo(x_834, x_837);
x_841 = lean_array_fset(x_839, x_831, x_840);
lean_dec(x_831);
lean_ctor_set(x_2, 1, x_841);
return x_2;
}
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; 
lean_dec(x_2);
x_842 = lean_ctor_get(x_816, 0);
lean_inc(x_842);
if (lean_is_exclusive(x_816)) {
 lean_ctor_release(x_816, 0);
 x_843 = x_816;
} else {
 lean_dec_ref(x_816);
 x_843 = lean_box(0);
}
x_844 = lean_box(0);
if (lean_is_scalar(x_843)) {
 x_845 = lean_alloc_ctor(1, 1, 0);
} else {
 x_845 = x_843;
}
lean_ctor_set(x_845, 0, x_1);
x_846 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_846, 0, x_844);
lean_ctor_set(x_846, 1, x_845);
lean_ctor_set(x_846, 2, x_844);
x_847 = lean_array_get_size(x_811);
x_848 = lean_nat_dec_lt(x_842, x_847);
lean_dec(x_847);
if (x_848 == 0)
{
lean_object* x_849; 
lean_dec(x_846);
lean_dec(x_842);
x_849 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_849, 0, x_3);
lean_ctor_set(x_849, 1, x_811);
return x_849;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_850 = lean_array_fget(x_811, x_842);
x_851 = lean_box(0);
x_852 = lean_array_fset(x_811, x_842, x_851);
x_853 = l_Lean_Syntax_setInfo(x_846, x_850);
x_854 = lean_array_fset(x_852, x_842, x_853);
lean_dec(x_842);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_3);
lean_ctor_set(x_855, 1, x_854);
return x_855;
}
}
}
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_856 = lean_ctor_get(x_2, 1);
lean_inc(x_856);
x_857 = l_Lean_Syntax_getArgs(x_2);
x_858 = lean_array_get_size(x_857);
x_859 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_860 = lean_unsigned_to_nat(0u);
x_861 = l_Array_findIdx_x3f_loop___rarg(x_857, x_859, x_858, x_860, lean_box(0));
lean_dec(x_857);
if (lean_obj_tag(x_861) == 0)
{
lean_dec(x_856);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_862; 
x_862 = !lean_is_exclusive(x_2);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; uint8_t x_865; 
x_863 = lean_ctor_get(x_2, 1);
lean_dec(x_863);
x_864 = lean_ctor_get(x_2, 0);
lean_dec(x_864);
x_865 = !lean_is_exclusive(x_861);
if (x_865 == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; uint8_t x_870; 
x_866 = lean_ctor_get(x_861, 0);
x_867 = lean_box(0);
lean_ctor_set(x_861, 0, x_1);
x_868 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_861);
lean_ctor_set(x_868, 2, x_867);
x_869 = lean_array_get_size(x_856);
x_870 = lean_nat_dec_lt(x_866, x_869);
lean_dec(x_869);
if (x_870 == 0)
{
lean_dec(x_868);
lean_dec(x_866);
return x_2;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_871 = lean_array_fget(x_856, x_866);
x_872 = lean_box(0);
x_873 = lean_array_fset(x_856, x_866, x_872);
x_874 = l_Lean_Syntax_setInfo(x_868, x_871);
x_875 = lean_array_fset(x_873, x_866, x_874);
lean_dec(x_866);
lean_ctor_set(x_2, 1, x_875);
return x_2;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; 
x_876 = lean_ctor_get(x_861, 0);
lean_inc(x_876);
lean_dec(x_861);
x_877 = lean_box(0);
x_878 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_878, 0, x_1);
x_879 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
lean_ctor_set(x_879, 2, x_877);
x_880 = lean_array_get_size(x_856);
x_881 = lean_nat_dec_lt(x_876, x_880);
lean_dec(x_880);
if (x_881 == 0)
{
lean_dec(x_879);
lean_dec(x_876);
return x_2;
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; 
x_882 = lean_array_fget(x_856, x_876);
x_883 = lean_box(0);
x_884 = lean_array_fset(x_856, x_876, x_883);
x_885 = l_Lean_Syntax_setInfo(x_879, x_882);
x_886 = lean_array_fset(x_884, x_876, x_885);
lean_dec(x_876);
lean_ctor_set(x_2, 1, x_886);
return x_2;
}
}
}
else
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; uint8_t x_893; 
lean_dec(x_2);
x_887 = lean_ctor_get(x_861, 0);
lean_inc(x_887);
if (lean_is_exclusive(x_861)) {
 lean_ctor_release(x_861, 0);
 x_888 = x_861;
} else {
 lean_dec_ref(x_861);
 x_888 = lean_box(0);
}
x_889 = lean_box(0);
if (lean_is_scalar(x_888)) {
 x_890 = lean_alloc_ctor(1, 1, 0);
} else {
 x_890 = x_888;
}
lean_ctor_set(x_890, 0, x_1);
x_891 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_891, 0, x_889);
lean_ctor_set(x_891, 1, x_890);
lean_ctor_set(x_891, 2, x_889);
x_892 = lean_array_get_size(x_856);
x_893 = lean_nat_dec_lt(x_887, x_892);
lean_dec(x_892);
if (x_893 == 0)
{
lean_object* x_894; 
lean_dec(x_891);
lean_dec(x_887);
x_894 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_894, 0, x_3);
lean_ctor_set(x_894, 1, x_856);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_895 = lean_array_fget(x_856, x_887);
x_896 = lean_box(0);
x_897 = lean_array_fset(x_856, x_887, x_896);
x_898 = l_Lean_Syntax_setInfo(x_891, x_895);
x_899 = lean_array_fset(x_897, x_887, x_898);
lean_dec(x_887);
x_900 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_900, 0, x_3);
lean_ctor_set(x_900, 1, x_899);
return x_900;
}
}
}
}
}
case 3:
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_901 = lean_box(0);
x_902 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_902, 0, x_1);
x_903 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set(x_903, 1, x_902);
lean_ctor_set(x_903, 2, x_901);
x_904 = l_Lean_Syntax_setInfo(x_903, x_2);
return x_904;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_8, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Name_isAnonymous(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_local_ctx_get_unused_name(x_9, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_905____closed__4;
x_14 = lean_local_ctx_get_unused_name(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getUnusedName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_bindingName_x21(x_9);
lean_dec(x_9);
lean_inc(x_3);
x_12 = l_Lean_PrettyPrinter_Delaborator_getUnusedName(x_11, x_2, x_3, x_4, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = lean_mk_syntax_ident(x_13);
lean_inc(x_2);
x_16 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_15, x_2, x_3, x_4, x_5, x_6, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_apply_1(x_1, x_17);
x_20 = l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(x_13, x_19, x_2, x_3, x_4, x_5, x_6, x_18);
return x_20;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_5(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabFor_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabFor_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = lean_apply_6(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_11, 1);
x_19 = lean_ctor_get(x_11, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
x_21 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_22 = lean_nat_dec_eq(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_free_object(x_11);
lean_dec(x_12);
x_1 = x_10;
x_7 = x_18;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_11, 1);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_ctor_get(x_12, 0);
lean_inc(x_25);
x_26 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_27 = lean_nat_dec_eq(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_dec(x_12);
x_1 = x_10;
x_7 = x_24;
goto _start;
}
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = l_Lean_PersistentEnvExtension_getState___rarg(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(x_16, x_1);
x_18 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_11);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_free_object(x_19);
lean_dec(x_21);
x_1 = x_18;
x_7 = x_22;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_31 = lean_nat_dec_eq(x_30, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_dec(x_27);
x_1 = x_18;
x_7 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(x_34, x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_18);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_36, x_2, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_35, 0);
lean_dec(x_41);
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_35);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_35, 1);
x_46 = lean_ctor_get(x_35, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
x_48 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_49 = lean_nat_dec_eq(x_48, x_47);
lean_dec(x_47);
if (x_49 == 0)
{
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
else
{
lean_free_object(x_35);
lean_dec(x_39);
x_1 = x_18;
x_7 = x_45;
goto _start;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_35, 1);
lean_inc(x_51);
lean_dec(x_35);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_54 = lean_nat_dec_eq(x_53, x_52);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_dec(x_39);
x_1 = x_18;
x_7 = x_51;
goto _start;
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("don't know how to delaborate '");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = l_Lean_PrettyPrinter_Delaborator_getExprKind(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_8);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_Lean_PrettyPrinter_Delaborator_delab___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_KernelException_toMessageData___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_15 = l_Lean_PrettyPrinter_Delaborator_delabFor(x_8, x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
x_25 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_26 = lean_nat_dec_eq(x_25, x_24);
lean_dec(x_24);
if (x_26 == 0)
{
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_15;
}
else
{
lean_object* x_27; 
lean_free_object(x_15);
lean_dec(x_16);
x_27 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(x_14, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
x_30 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_31 = lean_nat_dec_eq(x_30, x_29);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_16);
x_33 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(x_14, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
}
}
}
}
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appUnexpander");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Unexpander");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Register an unexpander for applications of a given constant.\n\n[appUnexpander c] registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant `c`. The unexpander is\npassed the result of pre-pretty printing the application *without* implicitly passed arguments. If `pp.explicit` is set\nto true or `pp.notation` is set to false, it will not be called at all.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5;
x_4 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
x_5 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("appUnexpanderAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.PrettyPrinter.delab");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
x_2 = l_Lean_PrettyPrinter_delab___closed__1;
x_3 = lean_unsigned_to_nat(284u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Syntax_strLitToAtom___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_delab___closed__3;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("input");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_delab___closed__4;
x_2 = l_Lean_PrettyPrinter_delab___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_40; lean_object* x_41; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_get(x_8, x_9);
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
x_40 = x_56;
x_41 = x_55;
goto block_50;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = l_Lean_PrettyPrinter_delab___closed__6;
x_59 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_58, x_5, x_6, x_7, x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unbox(x_60);
lean_dec(x_60);
x_40 = x_62;
x_41 = x_61;
goto block_50;
}
block_39:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_1);
lean_ctor_set(x_13, 5, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_PrettyPrinter_Delaborator_delab(x_13, x_5, x_6, x_7, x_8, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_23);
if (x_25 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_14);
lean_dec(x_15);
x_26 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_27 = l_Lean_PrettyPrinter_delab___closed__2;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = lean_apply_5(x_28, x_5, x_6, x_7, x_8, x_21);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
x_32 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
x_33 = lean_nat_dec_eq(x_32, x_31);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_15);
x_35 = l___private_Lean_Meta_WHNF_0__Lean_Meta_whnfEasyCases___closed__1;
x_36 = l_Lean_PrettyPrinter_delab___closed__2;
x_37 = lean_panic_fn(x_35, x_36);
x_38 = lean_apply_5(x_37, x_5, x_6, x_7, x_8, x_30);
return x_38;
}
}
}
}
}
block_50:
{
if (x_40 == 0)
{
x_10 = x_41;
goto block_39;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = l_Lean_fmt___at_Lean_ppExpr___spec__4(x_3);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_PrettyPrinter_delab___closed__6;
x_48 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_47, x_46, x_5, x_6, x_7, x_8, x_41);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_10 = x_49;
goto block_39;
}
}
}
}
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2038_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_delab___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(lean_object*);
lean_object* initialize_Lean_ProjFns(lean_object*);
lean_object* initialize_Lean_Syntax(lean_object*);
lean_object* initialize_Lean_Meta_Match(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lean_Meta_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Level_quote___lambda__2___closed__1 = _init_l_Lean_Level_quote___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Level_quote___lambda__2___closed__1);
l_Lean_Level_quote___lambda__4___closed__1 = _init_l_Lean_Level_quote___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Level_quote___lambda__4___closed__1);
l_Lean_Level_quote___lambda__4___closed__2 = _init_l_Lean_Level_quote___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Level_quote___lambda__4___closed__2);
l_Lean_Level_quote___lambda__6___closed__1 = _init_l_Lean_Level_quote___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Level_quote___lambda__6___closed__1);
l_Lean_Level_quote___lambda__6___closed__2 = _init_l_Lean_Level_quote___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Level_quote___lambda__6___closed__2);
l_Lean_Level_quote___closed__1 = _init_l_Lean_Level_quote___closed__1();
lean_mark_persistent(l_Lean_Level_quote___closed__1);
l_Lean_Level_quote___closed__2 = _init_l_Lean_Level_quote___closed__2();
lean_mark_persistent(l_Lean_Level_quote___closed__2);
l_Lean_Level_quote___closed__3 = _init_l_Lean_Level_quote___closed__3();
lean_mark_persistent(l_Lean_Level_quote___closed__3);
l_Lean_Level_quote___closed__4 = _init_l_Lean_Level_quote___closed__4();
lean_mark_persistent(l_Lean_Level_quote___closed__4);
l_Lean_Level_quote___closed__5 = _init_l_Lean_Level_quote___closed__5();
lean_mark_persistent(l_Lean_Level_quote___closed__5);
l_Lean_Level_quote___closed__6 = _init_l_Lean_Level_quote___closed__6();
lean_mark_persistent(l_Lean_Level_quote___closed__6);
l_Lean_Level_instQuoteLevel___closed__1 = _init_l_Lean_Level_instQuoteLevel___closed__1();
lean_mark_persistent(l_Lean_Level_instQuoteLevel___closed__1);
l_Lean_Level_instQuoteLevel = _init_l_Lean_Level_instQuoteLevel();
lean_mark_persistent(l_Lean_Level_instQuoteLevel);
l_Lean_getPPBinderTypes___closed__1 = _init_l_Lean_getPPBinderTypes___closed__1();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__1);
l_Lean_getPPBinderTypes___closed__2 = _init_l_Lean_getPPBinderTypes___closed__2();
lean_mark_persistent(l_Lean_getPPBinderTypes___closed__2);
l_Lean_getPPCoercions___closed__1 = _init_l_Lean_getPPCoercions___closed__1();
lean_mark_persistent(l_Lean_getPPCoercions___closed__1);
l_Lean_getPPCoercions___closed__2 = _init_l_Lean_getPPCoercions___closed__2();
lean_mark_persistent(l_Lean_getPPCoercions___closed__2);
l_Lean_getPPExplicit___closed__1 = _init_l_Lean_getPPExplicit___closed__1();
lean_mark_persistent(l_Lean_getPPExplicit___closed__1);
l_Lean_getPPNotation___closed__1 = _init_l_Lean_getPPNotation___closed__1();
lean_mark_persistent(l_Lean_getPPNotation___closed__1);
l_Lean_getPPNotation___closed__2 = _init_l_Lean_getPPNotation___closed__2();
lean_mark_persistent(l_Lean_getPPNotation___closed__2);
l_Lean_getPPStructureProjections___closed__1 = _init_l_Lean_getPPStructureProjections___closed__1();
lean_mark_persistent(l_Lean_getPPStructureProjections___closed__1);
l_Lean_getPPStructureProjections___closed__2 = _init_l_Lean_getPPStructureProjections___closed__2();
lean_mark_persistent(l_Lean_getPPStructureProjections___closed__2);
l_Lean_getPPStructureInstances___closed__1 = _init_l_Lean_getPPStructureInstances___closed__1();
lean_mark_persistent(l_Lean_getPPStructureInstances___closed__1);
l_Lean_getPPStructureInstances___closed__2 = _init_l_Lean_getPPStructureInstances___closed__2();
lean_mark_persistent(l_Lean_getPPStructureInstances___closed__2);
l_Lean_getPPStructureInstanceType___closed__1 = _init_l_Lean_getPPStructureInstanceType___closed__1();
lean_mark_persistent(l_Lean_getPPStructureInstanceType___closed__1);
l_Lean_getPPStructureInstanceType___closed__2 = _init_l_Lean_getPPStructureInstanceType___closed__2();
lean_mark_persistent(l_Lean_getPPStructureInstanceType___closed__2);
l_Lean_getPPUniverses___closed__1 = _init_l_Lean_getPPUniverses___closed__1();
lean_mark_persistent(l_Lean_getPPUniverses___closed__1);
l_Lean_getPPUniverses___closed__2 = _init_l_Lean_getPPUniverses___closed__2();
lean_mark_persistent(l_Lean_getPPUniverses___closed__2);
l_Lean_getPPFullNames___closed__1 = _init_l_Lean_getPPFullNames___closed__1();
lean_mark_persistent(l_Lean_getPPFullNames___closed__1);
l_Lean_getPPFullNames___closed__2 = _init_l_Lean_getPPFullNames___closed__2();
lean_mark_persistent(l_Lean_getPPFullNames___closed__2);
l_Lean_getPPPrivateNames___closed__1 = _init_l_Lean_getPPPrivateNames___closed__1();
lean_mark_persistent(l_Lean_getPPPrivateNames___closed__1);
l_Lean_getPPPrivateNames___closed__2 = _init_l_Lean_getPPPrivateNames___closed__2();
lean_mark_persistent(l_Lean_getPPPrivateNames___closed__2);
l_Lean_getPPUnicode___closed__1 = _init_l_Lean_getPPUnicode___closed__1();
lean_mark_persistent(l_Lean_getPPUnicode___closed__1);
l_Lean_getPPAll___closed__1 = _init_l_Lean_getPPAll___closed__1();
lean_mark_persistent(l_Lean_getPPAll___closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_554_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_Context_pos___default = _init_l_Lean_PrettyPrinter_Delaborator_Context_pos___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_Context_pos___default);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__1);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607____closed__2);
res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_607_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabFailureId);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM);
l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15);
res = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11);
l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2);
l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3);
l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4);
l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2);
l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2);
l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2);
l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1);
l_Lean_PrettyPrinter_Delaborator_delab___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__1);
l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__2);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7);
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8);
res = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute);
lean_dec_ref(res);
l_Lean_PrettyPrinter_delab___closed__1 = _init_l_Lean_PrettyPrinter_delab___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__1);
l_Lean_PrettyPrinter_delab___closed__2 = _init_l_Lean_PrettyPrinter_delab___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__2);
l_Lean_PrettyPrinter_delab___closed__3 = _init_l_Lean_PrettyPrinter_delab___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__3);
l_Lean_PrettyPrinter_delab___closed__4 = _init_l_Lean_PrettyPrinter_delab___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__4);
l_Lean_PrettyPrinter_delab___closed__5 = _init_l_Lean_PrettyPrinter_delab___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__5);
l_Lean_PrettyPrinter_delab___closed__6 = _init_l_Lean_PrettyPrinter_delab___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_delab___closed__6);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2038_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
