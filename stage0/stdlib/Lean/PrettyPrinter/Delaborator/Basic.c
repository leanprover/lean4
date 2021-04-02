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
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4;
extern lean_object* l_Lean_Expr_ctorName___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__1;
uint8_t lean_local_ctx_uses_user_name(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain(lean_object*);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFailureId;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_delab___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1;
lean_object* l_Lean_PrettyPrinter_delab___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__8;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPCoercions(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5;
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_936____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
uint8_t l_Lean_getPPExplicit(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1139____closed__26;
lean_object* l_Lean_getPPNotation___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_descend(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(lean_object*, size_t, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__8;
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487_(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2;
extern lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_KeyedDeclsAttribute_getValues___spec__1___rarg___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__3(lean_object*);
uint8_t l_Lean_getPPStructureProjections(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_getPPSafeShadowing(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPFullNames___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3;
uint8_t l_Lean_getPPUniverses(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1(lean_object*);
extern lean_object* l_Lean_instInhabitedException___closed__1;
uint8_t l_Lean_getPPBinderTypes(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_object*);
uint8_t l_Lean_getPPFullNames(lean_object*);
lean_object* l_Lean_pp_safe__shadowing;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4;
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_pp_notation;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingDomain___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pp_all;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_Context_pos___default;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1;
extern lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
lean_object* l_Lean_getPPUnicode___boxed(lean_object*);
lean_object* l_Lean_getPPUnicode___closed__1;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
lean_object* l_Lean_pp_structure__projections;
extern lean_object* l_Lean_Expr_ctorName___closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object*);
extern lean_object* l_Lean_Elab_autoBoundImplicitLocal___closed__1;
extern lean_object* l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6282____closed__20;
lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPStructureInstanceType(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPUnicode(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1;
lean_object* l_Lean_pp_private__names;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object*);
uint8_t l_Lean_getPPPrivateNames(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_pp_structure__instance__type;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3;
uint8_t l_Lean_getPPStructureInstances(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object*, lean_object*);
lean_object* l_Lean_pp_full__names;
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pp_explicit;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_setPPExplicit___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
lean_object* l_Lean_getPPCoercions___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4;
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__9;
uint8_t l_Lean_getPPNotation(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureInstanceType___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__1;
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_pp_coercions;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__2;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_format___closed__3;
extern lean_object* l_Lean_getSanitizeNames___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2(lean_object*);
lean_object* l_Lean_getPPAll___boxed(lean_object*);
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
lean_object* l_Lean_getPPStructureInstances___boxed(lean_object*);
lean_object* l_Lean_getPPUniverses___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
lean_object* l_Lean_getPPExplicit___boxed(lean_object*);
lean_object* l_Lean_pp_structure__instances;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2;
extern lean_object* l_Std_Format_getUnicode___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271_(lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
extern lean_object* l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2;
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
extern lean_object* l_Lean_Expr_ctorName___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_FindImpl_findM_x3f_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2123_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody(lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1(lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pp_universes;
lean_object* l_Lean_pp_binder__types;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__2;
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1;
extern lean_object* l_Lean_Expr_setPPUniverses___closed__2;
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3;
uint8_t l_Lean_getPPAll(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1;
lean_object* l_Lean_getPPPrivateNames___boxed(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__3;
lean_object* l_Lean_getPPStructureProjections___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3;
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadRef___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj___rarg___closed__2;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__1;
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPBinderTypes___boxed(lean_object*);
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display coercions, implicit parameters, proof terms, fully qualified names, universes, ");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("and disable beta reduction and notations during pretty printing");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_Parser_Command_notation___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) disable/enable notation (infix, mixfix, postfix operators and unicode characters)");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("coercions");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) hide coercion applications");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display universes");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Expr_setPPUniverses___closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("full_names");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display fully qualified names");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private_names");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display internal names assigned to private declarations");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("binder_types");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display types of lambda and Pi parameters");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_instances");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display structure instances using the '{ fieldName := fieldValue, ... }' notation ");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("or '⟨fieldValue, ... ⟩' if structure is tagged with [pp_using_anonymous_constructor] attribute");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_projections");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display structure projections using field notation");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display implicit arguments");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Expr_setPPExplicit___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structure_instance_type");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display type of structure instances");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("safe_shadowing");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) allow variable shadowing if there is no collision");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4;
x_4 = l_Lean_Option_register___at_Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Lean_getPPAll(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
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
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
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
uint8_t l_Lean_getPPBinderTypes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
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
uint8_t l_Lean_getPPCoercions(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (x_2 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_10, 0);
lean_dec(x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
}
}
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
uint8_t l_Lean_getPPExplicit(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_Expr_setPPExplicit___closed__1;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_2;
}
}
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
uint8_t l_Lean_getPPNotation(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (x_2 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_10, 0);
lean_dec(x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
}
}
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
uint8_t l_Lean_getPPStructureProjections(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (x_2 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_10, 0);
lean_dec(x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
}
}
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
uint8_t l_Lean_getPPStructureInstances(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (x_2 == 0)
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 1)
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_6);
x_8 = 1;
return x_8;
}
}
}
else
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
if (lean_obj_tag(x_10) == 1)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_10, 0);
lean_dec(x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
}
}
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
uint8_t l_Lean_getPPStructureInstanceType(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_2;
}
}
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
uint8_t l_Lean_getPPUniverses(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_Expr_setPPUniverses___closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_2;
}
}
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
uint8_t l_Lean_getPPFullNames(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_2;
}
}
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
uint8_t l_Lean_getPPPrivateNames(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2;
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_2;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
lean_dec(x_5);
return x_2;
}
}
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
x_2 = l_Std_Format_getUnicode___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
uint8_t l_Lean_getPPUnicode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_getPPUnicode___closed__1;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
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
uint8_t l_Lean_getPPSafeShadowing(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2;
x_3 = l_Lean_KVMap_findCore(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 1;
return x_7;
}
}
}
}
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_getPPSafeShadowing(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabFailure");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2;
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
x_1 = l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
x_2 = l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__4;
x_3 = l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__8;
x_4 = l_Lean_instMonadRef___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
x_4 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5;
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
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
return x_6;
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
x_1 = lean_mk_string("Delaborator");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Delab");
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
x_1 = lean_mk_string("Register a delaborator.\n\n  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`\n  constructor `k`. Multiple delaborators for a single constructor are tried in turn until\n  the first success. If the term to be delaborated is an application of a constant `c`,\n  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")\n  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`\n  is tried first.");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
x_4 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
x_5 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabAttribute");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
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
x_2 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1139____closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_2 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_6282____closed__20;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_apply_1(x_1, x_16);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
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
x_3 = lean_unsigned_to_nat(280u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Name_getString_x21___closed__3;
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
x_3 = lean_unsigned_to_nat(284u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Name_getString_x21___closed__3;
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
lean_object* x_4; 
x_4 = lean_apply_2(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg), 3, 0);
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
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_expandCoe___spec__7___rarg___lambda__1), 8, 2);
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
x_3 = lean_unsigned_to_nat(304u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Name_getString_x21___closed__3;
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
x_3 = lean_unsigned_to_nat(308u);
x_4 = lean_unsigned_to_nat(35u);
x_5 = l_Lean_Name_getString_x21___closed__3;
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
x_27 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
x_30 = l_Lean_Parser_Syntax_addPrec___closed__3;
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
x_38 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
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
x_46 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_61 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
x_64 = l_Lean_Parser_Syntax_addPrec___closed__3;
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
x_70 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
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
x_76 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_92 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
x_95 = l_Lean_Parser_Syntax_addPrec___closed__3;
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
x_102 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
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
x_109 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_129 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
x_132 = l_Lean_Parser_Syntax_addPrec___closed__3;
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
x_140 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
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
x_148 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_172 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
x_175 = l_Lean_Parser_Syntax_addPrec___closed__3;
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
x_184 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
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
x_193 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
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
x_20 = l_Lean_Parser_Syntax_addPrec___closed__1;
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_2, 1);
lean_dec(x_28);
x_29 = lean_ctor_get(x_2, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
lean_inc(x_1);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_1);
x_32 = lean_array_get_size(x_8);
x_33 = lean_nat_dec_lt(x_30, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
return x_2;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_array_fget(x_8, x_30);
x_35 = lean_box(0);
x_36 = lean_array_fset(x_8, x_30, x_35);
x_37 = l_Lean_Syntax_setInfo(x_31, x_34);
x_38 = lean_array_fset(x_36, x_30, x_37);
lean_dec(x_30);
lean_ctor_set(x_2, 1, x_38);
return x_2;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_2);
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
lean_inc(x_1);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_1);
x_41 = lean_array_get_size(x_8);
x_42 = lean_nat_dec_lt(x_39, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_8);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_array_fget(x_8, x_39);
x_45 = lean_box(0);
x_46 = lean_array_fset(x_8, x_39, x_45);
x_47 = l_Lean_Syntax_setInfo(x_40, x_44);
x_48 = lean_array_fset(x_46, x_39, x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_2);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_2, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_2, 0);
lean_dec(x_52);
x_53 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_54 = lean_string_dec_eq(x_15, x_53);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_3, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_3, 0);
lean_dec(x_57);
lean_ctor_set(x_6, 1, x_20);
lean_inc(x_8);
lean_inc(x_3);
x_58 = l_Lean_Syntax_getArgs(x_2);
x_59 = lean_array_get_size(x_58);
x_60 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Array_findIdx_x3f_loop___rarg(x_58, x_60, x_59, x_61, lean_box(0));
lean_dec(x_58);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_2);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec(x_62);
lean_inc(x_1);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_1);
x_65 = lean_array_get_size(x_8);
x_66 = lean_nat_dec_lt(x_63, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_63);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_3);
lean_ctor_set(x_67, 1, x_8);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_array_fget(x_8, x_63);
x_69 = lean_box(0);
x_70 = lean_array_fset(x_8, x_63, x_69);
x_71 = l_Lean_Syntax_setInfo(x_64, x_68);
x_72 = lean_array_fset(x_70, x_63, x_71);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_3);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
x_74 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_74, 0, x_4);
lean_ctor_set(x_74, 1, x_9);
lean_ctor_set_usize(x_74, 2, x_11);
lean_inc(x_8);
lean_inc(x_74);
lean_ctor_set(x_2, 0, x_74);
x_75 = l_Lean_Syntax_getArgs(x_2);
x_76 = lean_array_get_size(x_75);
x_77 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Array_findIdx_x3f_loop___rarg(x_75, x_77, x_76, x_78, lean_box(0));
lean_dec(x_75);
if (lean_obj_tag(x_79) == 0)
{
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_dec(x_2);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
lean_dec(x_79);
lean_inc(x_1);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_1);
x_82 = lean_array_get_size(x_8);
x_83 = lean_nat_dec_lt(x_80, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_81);
lean_dec(x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_8);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_array_fget(x_8, x_80);
x_86 = lean_box(0);
x_87 = lean_array_fset(x_8, x_80, x_86);
x_88 = l_Lean_Syntax_setInfo(x_81, x_85);
x_89 = lean_array_fset(x_87, x_80, x_88);
lean_dec(x_80);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_74);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_91; uint8_t x_92; 
lean_dec(x_15);
x_91 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_92 = lean_string_dec_eq(x_12, x_91);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_3);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_3, 1);
lean_dec(x_94);
x_95 = lean_ctor_get(x_3, 0);
lean_dec(x_95);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_53);
lean_inc(x_8);
lean_inc(x_3);
x_96 = l_Lean_Syntax_getArgs(x_2);
x_97 = lean_array_get_size(x_96);
x_98 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_99 = lean_unsigned_to_nat(0u);
x_100 = l_Array_findIdx_x3f_loop___rarg(x_96, x_98, x_97, x_99, lean_box(0));
lean_dec(x_96);
if (lean_obj_tag(x_100) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_2);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
lean_inc(x_1);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_1);
lean_ctor_set(x_102, 1, x_1);
x_103 = lean_array_get_size(x_8);
x_104 = lean_nat_dec_lt(x_101, x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_102);
lean_dec(x_101);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_3);
lean_ctor_set(x_105, 1, x_8);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_array_fget(x_8, x_101);
x_107 = lean_box(0);
x_108 = lean_array_fset(x_8, x_101, x_107);
x_109 = l_Lean_Syntax_setInfo(x_102, x_106);
x_110 = lean_array_fset(x_108, x_101, x_109);
lean_dec(x_101);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_3);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_53);
x_112 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_112, 0, x_4);
lean_ctor_set(x_112, 1, x_9);
lean_ctor_set_usize(x_112, 2, x_11);
lean_inc(x_8);
lean_inc(x_112);
lean_ctor_set(x_2, 0, x_112);
x_113 = l_Lean_Syntax_getArgs(x_2);
x_114 = lean_array_get_size(x_113);
x_115 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Array_findIdx_x3f_loop___rarg(x_113, x_115, x_114, x_116, lean_box(0));
lean_dec(x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_dec(x_112);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_2);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec(x_117);
lean_inc(x_1);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_1);
x_120 = lean_array_get_size(x_8);
x_121 = lean_nat_dec_lt(x_118, x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; 
lean_dec(x_119);
lean_dec(x_118);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_112);
lean_ctor_set(x_122, 1, x_8);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_array_fget(x_8, x_118);
x_124 = lean_box(0);
x_125 = lean_array_fset(x_8, x_118, x_124);
x_126 = l_Lean_Syntax_setInfo(x_119, x_123);
x_127 = lean_array_fset(x_125, x_118, x_126);
lean_dec(x_118);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_112);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_12);
x_129 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_130 = lean_string_dec_eq(x_9, x_129);
if (x_130 == 0)
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_3);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_3, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_3, 0);
lean_dec(x_133);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_53);
lean_ctor_set(x_4, 1, x_91);
lean_inc(x_8);
lean_inc(x_3);
x_134 = l_Lean_Syntax_getArgs(x_2);
x_135 = lean_array_get_size(x_134);
x_136 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_137 = lean_unsigned_to_nat(0u);
x_138 = l_Array_findIdx_x3f_loop___rarg(x_134, x_136, x_135, x_137, lean_box(0));
lean_dec(x_134);
if (lean_obj_tag(x_138) == 0)
{
lean_dec(x_3);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_2);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
lean_inc(x_1);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_1);
x_141 = lean_array_get_size(x_8);
x_142 = lean_nat_dec_lt(x_139, x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_3);
lean_ctor_set(x_143, 1, x_8);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_array_fget(x_8, x_139);
x_145 = lean_box(0);
x_146 = lean_array_fset(x_8, x_139, x_145);
x_147 = l_Lean_Syntax_setInfo(x_140, x_144);
x_148 = lean_array_fset(x_146, x_139, x_147);
lean_dec(x_139);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_3);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_53);
lean_ctor_set(x_4, 1, x_91);
x_150 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_9);
lean_ctor_set_usize(x_150, 2, x_11);
lean_inc(x_8);
lean_inc(x_150);
lean_ctor_set(x_2, 0, x_150);
x_151 = l_Lean_Syntax_getArgs(x_2);
x_152 = lean_array_get_size(x_151);
x_153 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_154 = lean_unsigned_to_nat(0u);
x_155 = l_Array_findIdx_x3f_loop___rarg(x_151, x_153, x_152, x_154, lean_box(0));
lean_dec(x_151);
if (lean_obj_tag(x_155) == 0)
{
lean_dec(x_150);
lean_dec(x_8);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_2);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
lean_dec(x_155);
lean_inc(x_1);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_1);
lean_ctor_set(x_157, 1, x_1);
x_158 = lean_array_get_size(x_8);
x_159 = lean_nat_dec_lt(x_156, x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; 
lean_dec(x_157);
lean_dec(x_156);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_8);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_array_fget(x_8, x_156);
x_162 = lean_box(0);
x_163 = lean_array_fset(x_8, x_156, x_162);
x_164 = l_Lean_Syntax_setInfo(x_157, x_161);
x_165 = lean_array_fset(x_163, x_156, x_164);
lean_dec(x_156);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_150);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_167 = lean_array_get_size(x_8);
x_168 = lean_unsigned_to_nat(0u);
x_169 = lean_nat_dec_lt(x_168, x_167);
lean_dec(x_167);
if (x_169 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_array_fget(x_8, x_168);
x_171 = lean_box(0);
x_172 = lean_array_fset(x_8, x_168, x_171);
x_173 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_170);
x_174 = lean_array_fset(x_172, x_168, x_173);
lean_ctor_set(x_2, 1, x_174);
return x_2;
}
}
}
}
}
else
{
lean_object* x_175; uint8_t x_176; 
lean_dec(x_2);
x_175 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_176 = lean_string_dec_eq(x_15, x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_177 = x_3;
} else {
 lean_dec_ref(x_3);
 x_177 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_4);
lean_ctor_set(x_178, 1, x_9);
lean_ctor_set_usize(x_178, 2, x_11);
lean_inc(x_8);
lean_inc(x_178);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_8);
x_180 = l_Lean_Syntax_getArgs(x_179);
x_181 = lean_array_get_size(x_180);
x_182 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_183 = lean_unsigned_to_nat(0u);
x_184 = l_Array_findIdx_x3f_loop___rarg(x_180, x_182, x_181, x_183, lean_box(0));
lean_dec(x_180);
if (lean_obj_tag(x_184) == 0)
{
lean_dec(x_178);
lean_dec(x_8);
lean_dec(x_1);
return x_179;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
lean_dec(x_179);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_1);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_1);
lean_ctor_set(x_186, 1, x_1);
x_187 = lean_array_get_size(x_8);
x_188 = lean_nat_dec_lt(x_185, x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; 
lean_dec(x_186);
lean_dec(x_185);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_178);
lean_ctor_set(x_189, 1, x_8);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_array_fget(x_8, x_185);
x_191 = lean_box(0);
x_192 = lean_array_fset(x_8, x_185, x_191);
x_193 = l_Lean_Syntax_setInfo(x_186, x_190);
x_194 = lean_array_fset(x_192, x_185, x_193);
lean_dec(x_185);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_178);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
lean_dec(x_15);
x_196 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_197 = lean_string_dec_eq(x_12, x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_198 = x_3;
} else {
 lean_dec_ref(x_3);
 x_198 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_175);
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_4);
lean_ctor_set(x_199, 1, x_9);
lean_ctor_set_usize(x_199, 2, x_11);
lean_inc(x_8);
lean_inc(x_199);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_8);
x_201 = l_Lean_Syntax_getArgs(x_200);
x_202 = lean_array_get_size(x_201);
x_203 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_findIdx_x3f_loop___rarg(x_201, x_203, x_202, x_204, lean_box(0));
lean_dec(x_201);
if (lean_obj_tag(x_205) == 0)
{
lean_dec(x_199);
lean_dec(x_8);
lean_dec(x_1);
return x_200;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
lean_dec(x_200);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec(x_205);
lean_inc(x_1);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_1);
lean_ctor_set(x_207, 1, x_1);
x_208 = lean_array_get_size(x_8);
x_209 = lean_nat_dec_lt(x_206, x_208);
lean_dec(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_207);
lean_dec(x_206);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_199);
lean_ctor_set(x_210, 1, x_8);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_211 = lean_array_fget(x_8, x_206);
x_212 = lean_box(0);
x_213 = lean_array_fset(x_8, x_206, x_212);
x_214 = l_Lean_Syntax_setInfo(x_207, x_211);
x_215 = lean_array_fset(x_213, x_206, x_214);
lean_dec(x_206);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_199);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; uint8_t x_218; 
lean_dec(x_12);
x_217 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_218 = lean_string_dec_eq(x_9, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_219 = x_3;
} else {
 lean_dec_ref(x_3);
 x_219 = lean_box(0);
}
lean_ctor_set(x_6, 1, x_20);
lean_ctor_set(x_5, 1, x_175);
lean_ctor_set(x_4, 1, x_196);
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_4);
lean_ctor_set(x_220, 1, x_9);
lean_ctor_set_usize(x_220, 2, x_11);
lean_inc(x_8);
lean_inc(x_220);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_8);
x_222 = l_Lean_Syntax_getArgs(x_221);
x_223 = lean_array_get_size(x_222);
x_224 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_225 = lean_unsigned_to_nat(0u);
x_226 = l_Array_findIdx_x3f_loop___rarg(x_222, x_224, x_223, x_225, lean_box(0));
lean_dec(x_222);
if (lean_obj_tag(x_226) == 0)
{
lean_dec(x_220);
lean_dec(x_8);
lean_dec(x_1);
return x_221;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_221);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
lean_inc(x_1);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_1);
lean_ctor_set(x_228, 1, x_1);
x_229 = lean_array_get_size(x_8);
x_230 = lean_nat_dec_lt(x_227, x_229);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_228);
lean_dec(x_227);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_220);
lean_ctor_set(x_231, 1, x_8);
return x_231;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_array_fget(x_8, x_227);
x_233 = lean_box(0);
x_234 = lean_array_fset(x_8, x_227, x_233);
x_235 = l_Lean_Syntax_setInfo(x_228, x_232);
x_236 = lean_array_fset(x_234, x_227, x_235);
lean_dec(x_227);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_220);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_238 = lean_array_get_size(x_8);
x_239 = lean_unsigned_to_nat(0u);
x_240 = lean_nat_dec_lt(x_239, x_238);
lean_dec(x_238);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_1);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_3);
lean_ctor_set(x_241, 1, x_8);
return x_241;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_242 = lean_array_fget(x_8, x_239);
x_243 = lean_box(0);
x_244 = lean_array_fset(x_8, x_239, x_243);
x_245 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_242);
x_246 = lean_array_fset(x_244, x_239, x_245);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_3);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
}
}
}
}
else
{
lean_object* x_248; size_t x_249; lean_object* x_250; uint8_t x_251; 
x_248 = lean_ctor_get(x_6, 1);
x_249 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_248);
lean_dec(x_6);
x_250 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_251 = lean_string_dec_eq(x_248, x_250);
lean_dec(x_248);
if (x_251 == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_free_object(x_5);
lean_dec(x_15);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_9);
x_252 = l_Lean_Syntax_getArgs(x_2);
x_253 = lean_array_get_size(x_252);
x_254 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_255 = lean_unsigned_to_nat(0u);
x_256 = l_Array_findIdx_x3f_loop___rarg(x_252, x_254, x_253, x_255, lean_box(0));
lean_dec(x_252);
if (lean_obj_tag(x_256) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_257 = x_2;
} else {
 lean_dec_ref(x_2);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_256, 0);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_1);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_1);
x_260 = lean_array_get_size(x_8);
x_261 = lean_nat_dec_lt(x_258, x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec(x_259);
lean_dec(x_258);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_257;
}
lean_ctor_set(x_262, 0, x_3);
lean_ctor_set(x_262, 1, x_8);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_array_fget(x_8, x_258);
x_264 = lean_box(0);
x_265 = lean_array_fset(x_8, x_258, x_264);
x_266 = l_Lean_Syntax_setInfo(x_259, x_263);
x_267 = lean_array_fset(x_265, x_258, x_266);
lean_dec(x_258);
if (lean_is_scalar(x_257)) {
 x_268 = lean_alloc_ctor(1, 2, 0);
} else {
 x_268 = x_257;
}
lean_ctor_set(x_268, 0, x_3);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; lean_object* x_270; uint8_t x_271; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_269 = x_2;
} else {
 lean_dec_ref(x_2);
 x_269 = lean_box(0);
}
x_270 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_271 = lean_string_dec_eq(x_15, x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_272 = x_3;
} else {
 lean_dec_ref(x_3);
 x_272 = lean_box(0);
}
x_273 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_273, 0, x_7);
lean_ctor_set(x_273, 1, x_250);
lean_ctor_set_usize(x_273, 2, x_249);
lean_ctor_set(x_5, 0, x_273);
if (lean_is_scalar(x_272)) {
 x_274 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_274 = x_272;
}
lean_ctor_set(x_274, 0, x_4);
lean_ctor_set(x_274, 1, x_9);
lean_ctor_set_usize(x_274, 2, x_11);
lean_inc(x_8);
lean_inc(x_274);
if (lean_is_scalar(x_269)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_269;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_8);
x_276 = l_Lean_Syntax_getArgs(x_275);
x_277 = lean_array_get_size(x_276);
x_278 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_279 = lean_unsigned_to_nat(0u);
x_280 = l_Array_findIdx_x3f_loop___rarg(x_276, x_278, x_277, x_279, lean_box(0));
lean_dec(x_276);
if (lean_obj_tag(x_280) == 0)
{
lean_dec(x_274);
lean_dec(x_8);
lean_dec(x_1);
return x_275;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_275);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
lean_dec(x_280);
lean_inc(x_1);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_1);
lean_ctor_set(x_282, 1, x_1);
x_283 = lean_array_get_size(x_8);
x_284 = lean_nat_dec_lt(x_281, x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; 
lean_dec(x_282);
lean_dec(x_281);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_274);
lean_ctor_set(x_285, 1, x_8);
return x_285;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_286 = lean_array_fget(x_8, x_281);
x_287 = lean_box(0);
x_288 = lean_array_fset(x_8, x_281, x_287);
x_289 = l_Lean_Syntax_setInfo(x_282, x_286);
x_290 = lean_array_fset(x_288, x_281, x_289);
lean_dec(x_281);
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_274);
lean_ctor_set(x_291, 1, x_290);
return x_291;
}
}
}
else
{
lean_object* x_292; uint8_t x_293; 
lean_dec(x_15);
x_292 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_293 = lean_string_dec_eq(x_12, x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_294 = x_3;
} else {
 lean_dec_ref(x_3);
 x_294 = lean_box(0);
}
x_295 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_295, 0, x_7);
lean_ctor_set(x_295, 1, x_250);
lean_ctor_set_usize(x_295, 2, x_249);
lean_ctor_set(x_5, 1, x_270);
lean_ctor_set(x_5, 0, x_295);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_4);
lean_ctor_set(x_296, 1, x_9);
lean_ctor_set_usize(x_296, 2, x_11);
lean_inc(x_8);
lean_inc(x_296);
if (lean_is_scalar(x_269)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_269;
}
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
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
lean_dec(x_297);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec(x_302);
lean_inc(x_1);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_1);
lean_ctor_set(x_304, 1, x_1);
x_305 = lean_array_get_size(x_8);
x_306 = lean_nat_dec_lt(x_303, x_305);
lean_dec(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
lean_dec(x_304);
lean_dec(x_303);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_296);
lean_ctor_set(x_307, 1, x_8);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_308 = lean_array_fget(x_8, x_303);
x_309 = lean_box(0);
x_310 = lean_array_fset(x_8, x_303, x_309);
x_311 = l_Lean_Syntax_setInfo(x_304, x_308);
x_312 = lean_array_fset(x_310, x_303, x_311);
lean_dec(x_303);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_296);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; uint8_t x_315; 
lean_dec(x_12);
x_314 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_315 = lean_string_dec_eq(x_9, x_314);
if (x_315 == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_316 = x_3;
} else {
 lean_dec_ref(x_3);
 x_316 = lean_box(0);
}
x_317 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_317, 0, x_7);
lean_ctor_set(x_317, 1, x_250);
lean_ctor_set_usize(x_317, 2, x_249);
lean_ctor_set(x_5, 1, x_270);
lean_ctor_set(x_5, 0, x_317);
lean_ctor_set(x_4, 1, x_292);
if (lean_is_scalar(x_316)) {
 x_318 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_318 = x_316;
}
lean_ctor_set(x_318, 0, x_4);
lean_ctor_set(x_318, 1, x_9);
lean_ctor_set_usize(x_318, 2, x_11);
lean_inc(x_8);
lean_inc(x_318);
if (lean_is_scalar(x_269)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_269;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_8);
x_320 = l_Lean_Syntax_getArgs(x_319);
x_321 = lean_array_get_size(x_320);
x_322 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_323 = lean_unsigned_to_nat(0u);
x_324 = l_Array_findIdx_x3f_loop___rarg(x_320, x_322, x_321, x_323, lean_box(0));
lean_dec(x_320);
if (lean_obj_tag(x_324) == 0)
{
lean_dec(x_318);
lean_dec(x_8);
lean_dec(x_1);
return x_319;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
lean_dec(x_319);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
lean_dec(x_324);
lean_inc(x_1);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_1);
lean_ctor_set(x_326, 1, x_1);
x_327 = lean_array_get_size(x_8);
x_328 = lean_nat_dec_lt(x_325, x_327);
lean_dec(x_327);
if (x_328 == 0)
{
lean_object* x_329; 
lean_dec(x_326);
lean_dec(x_325);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_318);
lean_ctor_set(x_329, 1, x_8);
return x_329;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_array_fget(x_8, x_325);
x_331 = lean_box(0);
x_332 = lean_array_fset(x_8, x_325, x_331);
x_333 = l_Lean_Syntax_setInfo(x_326, x_330);
x_334 = lean_array_fset(x_332, x_325, x_333);
lean_dec(x_325);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_318);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; 
lean_free_object(x_5);
lean_free_object(x_4);
lean_dec(x_9);
x_336 = lean_array_get_size(x_8);
x_337 = lean_unsigned_to_nat(0u);
x_338 = lean_nat_dec_lt(x_337, x_336);
lean_dec(x_336);
if (x_338 == 0)
{
lean_object* x_339; 
lean_dec(x_1);
if (lean_is_scalar(x_269)) {
 x_339 = lean_alloc_ctor(1, 2, 0);
} else {
 x_339 = x_269;
}
lean_ctor_set(x_339, 0, x_3);
lean_ctor_set(x_339, 1, x_8);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_340 = lean_array_fget(x_8, x_337);
x_341 = lean_box(0);
x_342 = lean_array_fset(x_8, x_337, x_341);
x_343 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_340);
x_344 = lean_array_fset(x_342, x_337, x_343);
if (lean_is_scalar(x_269)) {
 x_345 = lean_alloc_ctor(1, 2, 0);
} else {
 x_345 = x_269;
}
lean_ctor_set(x_345, 0, x_3);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
}
}
}
}
else
{
lean_object* x_346; size_t x_347; lean_object* x_348; size_t x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_346 = lean_ctor_get(x_5, 1);
x_347 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_346);
lean_dec(x_5);
x_348 = lean_ctor_get(x_6, 1);
lean_inc(x_348);
x_349 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_350 = x_6;
} else {
 lean_dec_ref(x_6);
 x_350 = lean_box(0);
}
x_351 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_352 = lean_string_dec_eq(x_348, x_351);
lean_dec(x_348);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_350);
lean_dec(x_346);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_9);
x_353 = l_Lean_Syntax_getArgs(x_2);
x_354 = lean_array_get_size(x_353);
x_355 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_356 = lean_unsigned_to_nat(0u);
x_357 = l_Array_findIdx_x3f_loop___rarg(x_353, x_355, x_354, x_356, lean_box(0));
lean_dec(x_353);
if (lean_obj_tag(x_357) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_358 = x_2;
} else {
 lean_dec_ref(x_2);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_357, 0);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_1);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_1);
lean_ctor_set(x_360, 1, x_1);
x_361 = lean_array_get_size(x_8);
x_362 = lean_nat_dec_lt(x_359, x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; 
lean_dec(x_360);
lean_dec(x_359);
if (lean_is_scalar(x_358)) {
 x_363 = lean_alloc_ctor(1, 2, 0);
} else {
 x_363 = x_358;
}
lean_ctor_set(x_363, 0, x_3);
lean_ctor_set(x_363, 1, x_8);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_364 = lean_array_fget(x_8, x_359);
x_365 = lean_box(0);
x_366 = lean_array_fset(x_8, x_359, x_365);
x_367 = l_Lean_Syntax_setInfo(x_360, x_364);
x_368 = lean_array_fset(x_366, x_359, x_367);
lean_dec(x_359);
if (lean_is_scalar(x_358)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_358;
}
lean_ctor_set(x_369, 0, x_3);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_370 = x_2;
} else {
 lean_dec_ref(x_2);
 x_370 = lean_box(0);
}
x_371 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_372 = lean_string_dec_eq(x_346, x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_373 = x_3;
} else {
 lean_dec_ref(x_3);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_374 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_374 = x_350;
}
lean_ctor_set(x_374, 0, x_7);
lean_ctor_set(x_374, 1, x_351);
lean_ctor_set_usize(x_374, 2, x_349);
x_375 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_346);
lean_ctor_set_usize(x_375, 2, x_347);
lean_ctor_set(x_4, 0, x_375);
if (lean_is_scalar(x_373)) {
 x_376 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_376 = x_373;
}
lean_ctor_set(x_376, 0, x_4);
lean_ctor_set(x_376, 1, x_9);
lean_ctor_set_usize(x_376, 2, x_11);
lean_inc(x_8);
lean_inc(x_376);
if (lean_is_scalar(x_370)) {
 x_377 = lean_alloc_ctor(1, 2, 0);
} else {
 x_377 = x_370;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_8);
x_378 = l_Lean_Syntax_getArgs(x_377);
x_379 = lean_array_get_size(x_378);
x_380 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_381 = lean_unsigned_to_nat(0u);
x_382 = l_Array_findIdx_x3f_loop___rarg(x_378, x_380, x_379, x_381, lean_box(0));
lean_dec(x_378);
if (lean_obj_tag(x_382) == 0)
{
lean_dec(x_376);
lean_dec(x_8);
lean_dec(x_1);
return x_377;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
lean_dec(x_377);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
lean_dec(x_382);
lean_inc(x_1);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_1);
lean_ctor_set(x_384, 1, x_1);
x_385 = lean_array_get_size(x_8);
x_386 = lean_nat_dec_lt(x_383, x_385);
lean_dec(x_385);
if (x_386 == 0)
{
lean_object* x_387; 
lean_dec(x_384);
lean_dec(x_383);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_376);
lean_ctor_set(x_387, 1, x_8);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_388 = lean_array_fget(x_8, x_383);
x_389 = lean_box(0);
x_390 = lean_array_fset(x_8, x_383, x_389);
x_391 = l_Lean_Syntax_setInfo(x_384, x_388);
x_392 = lean_array_fset(x_390, x_383, x_391);
lean_dec(x_383);
x_393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_393, 0, x_376);
lean_ctor_set(x_393, 1, x_392);
return x_393;
}
}
}
else
{
lean_object* x_394; uint8_t x_395; 
lean_dec(x_346);
x_394 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_395 = lean_string_dec_eq(x_12, x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_396 = x_3;
} else {
 lean_dec_ref(x_3);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_397 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_397 = x_350;
}
lean_ctor_set(x_397, 0, x_7);
lean_ctor_set(x_397, 1, x_351);
lean_ctor_set_usize(x_397, 2, x_349);
x_398 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_371);
lean_ctor_set_usize(x_398, 2, x_347);
lean_ctor_set(x_4, 0, x_398);
if (lean_is_scalar(x_396)) {
 x_399 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_399 = x_396;
}
lean_ctor_set(x_399, 0, x_4);
lean_ctor_set(x_399, 1, x_9);
lean_ctor_set_usize(x_399, 2, x_11);
lean_inc(x_8);
lean_inc(x_399);
if (lean_is_scalar(x_370)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_370;
}
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_8);
x_401 = l_Lean_Syntax_getArgs(x_400);
x_402 = lean_array_get_size(x_401);
x_403 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_404 = lean_unsigned_to_nat(0u);
x_405 = l_Array_findIdx_x3f_loop___rarg(x_401, x_403, x_402, x_404, lean_box(0));
lean_dec(x_401);
if (lean_obj_tag(x_405) == 0)
{
lean_dec(x_399);
lean_dec(x_8);
lean_dec(x_1);
return x_400;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; uint8_t x_409; 
lean_dec(x_400);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
lean_dec(x_405);
lean_inc(x_1);
x_407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_407, 0, x_1);
lean_ctor_set(x_407, 1, x_1);
x_408 = lean_array_get_size(x_8);
x_409 = lean_nat_dec_lt(x_406, x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; 
lean_dec(x_407);
lean_dec(x_406);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_399);
lean_ctor_set(x_410, 1, x_8);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_array_fget(x_8, x_406);
x_412 = lean_box(0);
x_413 = lean_array_fset(x_8, x_406, x_412);
x_414 = l_Lean_Syntax_setInfo(x_407, x_411);
x_415 = lean_array_fset(x_413, x_406, x_414);
lean_dec(x_406);
x_416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_416, 0, x_399);
lean_ctor_set(x_416, 1, x_415);
return x_416;
}
}
}
else
{
lean_object* x_417; uint8_t x_418; 
lean_dec(x_12);
x_417 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_418 = lean_string_dec_eq(x_9, x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_419 = x_3;
} else {
 lean_dec_ref(x_3);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_350)) {
 x_420 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_420 = x_350;
}
lean_ctor_set(x_420, 0, x_7);
lean_ctor_set(x_420, 1, x_351);
lean_ctor_set_usize(x_420, 2, x_349);
x_421 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_371);
lean_ctor_set_usize(x_421, 2, x_347);
lean_ctor_set(x_4, 1, x_394);
lean_ctor_set(x_4, 0, x_421);
if (lean_is_scalar(x_419)) {
 x_422 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_422 = x_419;
}
lean_ctor_set(x_422, 0, x_4);
lean_ctor_set(x_422, 1, x_9);
lean_ctor_set_usize(x_422, 2, x_11);
lean_inc(x_8);
lean_inc(x_422);
if (lean_is_scalar(x_370)) {
 x_423 = lean_alloc_ctor(1, 2, 0);
} else {
 x_423 = x_370;
}
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_8);
x_424 = l_Lean_Syntax_getArgs(x_423);
x_425 = lean_array_get_size(x_424);
x_426 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_427 = lean_unsigned_to_nat(0u);
x_428 = l_Array_findIdx_x3f_loop___rarg(x_424, x_426, x_425, x_427, lean_box(0));
lean_dec(x_424);
if (lean_obj_tag(x_428) == 0)
{
lean_dec(x_422);
lean_dec(x_8);
lean_dec(x_1);
return x_423;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; 
lean_dec(x_423);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
lean_dec(x_428);
lean_inc(x_1);
x_430 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_430, 0, x_1);
lean_ctor_set(x_430, 1, x_1);
x_431 = lean_array_get_size(x_8);
x_432 = lean_nat_dec_lt(x_429, x_431);
lean_dec(x_431);
if (x_432 == 0)
{
lean_object* x_433; 
lean_dec(x_430);
lean_dec(x_429);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_422);
lean_ctor_set(x_433, 1, x_8);
return x_433;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_434 = lean_array_fget(x_8, x_429);
x_435 = lean_box(0);
x_436 = lean_array_fset(x_8, x_429, x_435);
x_437 = l_Lean_Syntax_setInfo(x_430, x_434);
x_438 = lean_array_fset(x_436, x_429, x_437);
lean_dec(x_429);
x_439 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_439, 0, x_422);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
}
else
{
lean_object* x_440; lean_object* x_441; uint8_t x_442; 
lean_dec(x_350);
lean_free_object(x_4);
lean_dec(x_9);
x_440 = lean_array_get_size(x_8);
x_441 = lean_unsigned_to_nat(0u);
x_442 = lean_nat_dec_lt(x_441, x_440);
lean_dec(x_440);
if (x_442 == 0)
{
lean_object* x_443; 
lean_dec(x_1);
if (lean_is_scalar(x_370)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_370;
}
lean_ctor_set(x_443, 0, x_3);
lean_ctor_set(x_443, 1, x_8);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_444 = lean_array_fget(x_8, x_441);
x_445 = lean_box(0);
x_446 = lean_array_fset(x_8, x_441, x_445);
x_447 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_444);
x_448 = lean_array_fset(x_446, x_441, x_447);
if (lean_is_scalar(x_370)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_370;
}
lean_ctor_set(x_449, 0, x_3);
lean_ctor_set(x_449, 1, x_448);
return x_449;
}
}
}
}
}
}
}
else
{
size_t x_450; lean_object* x_451; size_t x_452; lean_object* x_453; size_t x_454; lean_object* x_455; lean_object* x_456; size_t x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_450 = lean_ctor_get_usize(x_3, 2);
x_451 = lean_ctor_get(x_4, 1);
x_452 = lean_ctor_get_usize(x_4, 2);
lean_inc(x_451);
lean_dec(x_4);
x_453 = lean_ctor_get(x_5, 1);
lean_inc(x_453);
x_454 = lean_ctor_get_usize(x_5, 2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_455 = x_5;
} else {
 lean_dec_ref(x_5);
 x_455 = lean_box(0);
}
x_456 = lean_ctor_get(x_6, 1);
lean_inc(x_456);
x_457 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_458 = x_6;
} else {
 lean_dec_ref(x_6);
 x_458 = lean_box(0);
}
x_459 = l_Lean_Parser_Syntax_addPrec___closed__1;
x_460 = lean_string_dec_eq(x_456, x_459);
lean_dec(x_456);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_458);
lean_dec(x_455);
lean_dec(x_453);
lean_dec(x_451);
lean_dec(x_9);
x_461 = l_Lean_Syntax_getArgs(x_2);
x_462 = lean_array_get_size(x_461);
x_463 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_464 = lean_unsigned_to_nat(0u);
x_465 = l_Array_findIdx_x3f_loop___rarg(x_461, x_463, x_462, x_464, lean_box(0));
lean_dec(x_461);
if (lean_obj_tag(x_465) == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_466 = x_2;
} else {
 lean_dec_ref(x_2);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_465, 0);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_1);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_1);
lean_ctor_set(x_468, 1, x_1);
x_469 = lean_array_get_size(x_8);
x_470 = lean_nat_dec_lt(x_467, x_469);
lean_dec(x_469);
if (x_470 == 0)
{
lean_object* x_471; 
lean_dec(x_468);
lean_dec(x_467);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_466;
}
lean_ctor_set(x_471, 0, x_3);
lean_ctor_set(x_471, 1, x_8);
return x_471;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_472 = lean_array_fget(x_8, x_467);
x_473 = lean_box(0);
x_474 = lean_array_fset(x_8, x_467, x_473);
x_475 = l_Lean_Syntax_setInfo(x_468, x_472);
x_476 = lean_array_fset(x_474, x_467, x_475);
lean_dec(x_467);
if (lean_is_scalar(x_466)) {
 x_477 = lean_alloc_ctor(1, 2, 0);
} else {
 x_477 = x_466;
}
lean_ctor_set(x_477, 0, x_3);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
else
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_478 = x_2;
} else {
 lean_dec_ref(x_2);
 x_478 = lean_box(0);
}
x_479 = l_Lean_Parser_Syntax_addPrec___closed__3;
x_480 = lean_string_dec_eq(x_453, x_479);
if (x_480 == 0)
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_481 = x_3;
} else {
 lean_dec_ref(x_3);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_482 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_482 = x_458;
}
lean_ctor_set(x_482, 0, x_7);
lean_ctor_set(x_482, 1, x_459);
lean_ctor_set_usize(x_482, 2, x_457);
if (lean_is_scalar(x_455)) {
 x_483 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_483 = x_455;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_453);
lean_ctor_set_usize(x_483, 2, x_454);
x_484 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_451);
lean_ctor_set_usize(x_484, 2, x_452);
if (lean_is_scalar(x_481)) {
 x_485 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_485 = x_481;
}
lean_ctor_set(x_485, 0, x_484);
lean_ctor_set(x_485, 1, x_9);
lean_ctor_set_usize(x_485, 2, x_450);
lean_inc(x_8);
lean_inc(x_485);
if (lean_is_scalar(x_478)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_478;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_8);
x_487 = l_Lean_Syntax_getArgs(x_486);
x_488 = lean_array_get_size(x_487);
x_489 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_490 = lean_unsigned_to_nat(0u);
x_491 = l_Array_findIdx_x3f_loop___rarg(x_487, x_489, x_488, x_490, lean_box(0));
lean_dec(x_487);
if (lean_obj_tag(x_491) == 0)
{
lean_dec(x_485);
lean_dec(x_8);
lean_dec(x_1);
return x_486;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
lean_dec(x_486);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
lean_dec(x_491);
lean_inc(x_1);
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_1);
lean_ctor_set(x_493, 1, x_1);
x_494 = lean_array_get_size(x_8);
x_495 = lean_nat_dec_lt(x_492, x_494);
lean_dec(x_494);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_493);
lean_dec(x_492);
x_496 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_496, 0, x_485);
lean_ctor_set(x_496, 1, x_8);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_497 = lean_array_fget(x_8, x_492);
x_498 = lean_box(0);
x_499 = lean_array_fset(x_8, x_492, x_498);
x_500 = l_Lean_Syntax_setInfo(x_493, x_497);
x_501 = lean_array_fset(x_499, x_492, x_500);
lean_dec(x_492);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_485);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
else
{
lean_object* x_503; uint8_t x_504; 
lean_dec(x_453);
x_503 = l_myMacro____x40_Init_Notation___hyg_2278____closed__1;
x_504 = lean_string_dec_eq(x_451, x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_505 = x_3;
} else {
 lean_dec_ref(x_3);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_506 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_506 = x_458;
}
lean_ctor_set(x_506, 0, x_7);
lean_ctor_set(x_506, 1, x_459);
lean_ctor_set_usize(x_506, 2, x_457);
if (lean_is_scalar(x_455)) {
 x_507 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_507 = x_455;
}
lean_ctor_set(x_507, 0, x_506);
lean_ctor_set(x_507, 1, x_479);
lean_ctor_set_usize(x_507, 2, x_454);
x_508 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_451);
lean_ctor_set_usize(x_508, 2, x_452);
if (lean_is_scalar(x_505)) {
 x_509 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_509 = x_505;
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_9);
lean_ctor_set_usize(x_509, 2, x_450);
lean_inc(x_8);
lean_inc(x_509);
if (lean_is_scalar(x_478)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_478;
}
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_8);
x_511 = l_Lean_Syntax_getArgs(x_510);
x_512 = lean_array_get_size(x_511);
x_513 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_514 = lean_unsigned_to_nat(0u);
x_515 = l_Array_findIdx_x3f_loop___rarg(x_511, x_513, x_512, x_514, lean_box(0));
lean_dec(x_511);
if (lean_obj_tag(x_515) == 0)
{
lean_dec(x_509);
lean_dec(x_8);
lean_dec(x_1);
return x_510;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; 
lean_dec(x_510);
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
lean_dec(x_515);
lean_inc(x_1);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_1);
lean_ctor_set(x_517, 1, x_1);
x_518 = lean_array_get_size(x_8);
x_519 = lean_nat_dec_lt(x_516, x_518);
lean_dec(x_518);
if (x_519 == 0)
{
lean_object* x_520; 
lean_dec(x_517);
lean_dec(x_516);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_509);
lean_ctor_set(x_520, 1, x_8);
return x_520;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_521 = lean_array_fget(x_8, x_516);
x_522 = lean_box(0);
x_523 = lean_array_fset(x_8, x_516, x_522);
x_524 = l_Lean_Syntax_setInfo(x_517, x_521);
x_525 = lean_array_fset(x_523, x_516, x_524);
lean_dec(x_516);
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_509);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
}
else
{
lean_object* x_527; uint8_t x_528; 
lean_dec(x_451);
x_527 = l_myMacro____x40_Init_Notation___hyg_2278____closed__3;
x_528 = lean_string_dec_eq(x_9, x_527);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_529 = x_3;
} else {
 lean_dec_ref(x_3);
 x_529 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_530 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_530 = x_458;
}
lean_ctor_set(x_530, 0, x_7);
lean_ctor_set(x_530, 1, x_459);
lean_ctor_set_usize(x_530, 2, x_457);
if (lean_is_scalar(x_455)) {
 x_531 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_531 = x_455;
}
lean_ctor_set(x_531, 0, x_530);
lean_ctor_set(x_531, 1, x_479);
lean_ctor_set_usize(x_531, 2, x_454);
x_532 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_532, 0, x_531);
lean_ctor_set(x_532, 1, x_503);
lean_ctor_set_usize(x_532, 2, x_452);
if (lean_is_scalar(x_529)) {
 x_533 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_533 = x_529;
}
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_9);
lean_ctor_set_usize(x_533, 2, x_450);
lean_inc(x_8);
lean_inc(x_533);
if (lean_is_scalar(x_478)) {
 x_534 = lean_alloc_ctor(1, 2, 0);
} else {
 x_534 = x_478;
}
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_8);
x_535 = l_Lean_Syntax_getArgs(x_534);
x_536 = lean_array_get_size(x_535);
x_537 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_538 = lean_unsigned_to_nat(0u);
x_539 = l_Array_findIdx_x3f_loop___rarg(x_535, x_537, x_536, x_538, lean_box(0));
lean_dec(x_535);
if (lean_obj_tag(x_539) == 0)
{
lean_dec(x_533);
lean_dec(x_8);
lean_dec(x_1);
return x_534;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
lean_dec(x_534);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
lean_dec(x_539);
lean_inc(x_1);
x_541 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_541, 0, x_1);
lean_ctor_set(x_541, 1, x_1);
x_542 = lean_array_get_size(x_8);
x_543 = lean_nat_dec_lt(x_540, x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
lean_dec(x_541);
lean_dec(x_540);
x_544 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_544, 0, x_533);
lean_ctor_set(x_544, 1, x_8);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_545 = lean_array_fget(x_8, x_540);
x_546 = lean_box(0);
x_547 = lean_array_fset(x_8, x_540, x_546);
x_548 = l_Lean_Syntax_setInfo(x_541, x_545);
x_549 = lean_array_fset(x_547, x_540, x_548);
lean_dec(x_540);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_533);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; uint8_t x_553; 
lean_dec(x_458);
lean_dec(x_455);
lean_dec(x_9);
x_551 = lean_array_get_size(x_8);
x_552 = lean_unsigned_to_nat(0u);
x_553 = lean_nat_dec_lt(x_552, x_551);
lean_dec(x_551);
if (x_553 == 0)
{
lean_object* x_554; 
lean_dec(x_1);
if (lean_is_scalar(x_478)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_478;
}
lean_ctor_set(x_554, 0, x_3);
lean_ctor_set(x_554, 1, x_8);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_555 = lean_array_fget(x_8, x_552);
x_556 = lean_box(0);
x_557 = lean_array_fset(x_8, x_552, x_556);
x_558 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_1, x_555);
x_559 = lean_array_fset(x_557, x_552, x_558);
if (lean_is_scalar(x_478)) {
 x_560 = lean_alloc_ctor(1, 2, 0);
} else {
 x_560 = x_478;
}
lean_ctor_set(x_560, 0, x_3);
lean_ctor_set(x_560, 1, x_559);
return x_560;
}
}
}
}
}
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_561 = lean_ctor_get(x_2, 1);
lean_inc(x_561);
x_562 = l_Lean_Syntax_getArgs(x_2);
x_563 = lean_array_get_size(x_562);
x_564 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_565 = lean_unsigned_to_nat(0u);
x_566 = l_Array_findIdx_x3f_loop___rarg(x_562, x_564, x_563, x_565, lean_box(0));
lean_dec(x_562);
if (lean_obj_tag(x_566) == 0)
{
lean_dec(x_561);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_567; 
x_567 = !lean_is_exclusive(x_2);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; uint8_t x_573; 
x_568 = lean_ctor_get(x_2, 1);
lean_dec(x_568);
x_569 = lean_ctor_get(x_2, 0);
lean_dec(x_569);
x_570 = lean_ctor_get(x_566, 0);
lean_inc(x_570);
lean_dec(x_566);
lean_inc(x_1);
x_571 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_571, 0, x_1);
lean_ctor_set(x_571, 1, x_1);
x_572 = lean_array_get_size(x_561);
x_573 = lean_nat_dec_lt(x_570, x_572);
lean_dec(x_572);
if (x_573 == 0)
{
lean_dec(x_571);
lean_dec(x_570);
return x_2;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_574 = lean_array_fget(x_561, x_570);
x_575 = lean_box(0);
x_576 = lean_array_fset(x_561, x_570, x_575);
x_577 = l_Lean_Syntax_setInfo(x_571, x_574);
x_578 = lean_array_fset(x_576, x_570, x_577);
lean_dec(x_570);
lean_ctor_set(x_2, 1, x_578);
return x_2;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
lean_dec(x_2);
x_579 = lean_ctor_get(x_566, 0);
lean_inc(x_579);
lean_dec(x_566);
lean_inc(x_1);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_1);
lean_ctor_set(x_580, 1, x_1);
x_581 = lean_array_get_size(x_561);
x_582 = lean_nat_dec_lt(x_579, x_581);
lean_dec(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
lean_dec(x_580);
lean_dec(x_579);
x_583 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_583, 0, x_3);
lean_ctor_set(x_583, 1, x_561);
return x_583;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_584 = lean_array_fget(x_561, x_579);
x_585 = lean_box(0);
x_586 = lean_array_fset(x_561, x_579, x_585);
x_587 = l_Lean_Syntax_setInfo(x_580, x_584);
x_588 = lean_array_fset(x_586, x_579, x_587);
lean_dec(x_579);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_3);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_590 = lean_ctor_get(x_2, 1);
lean_inc(x_590);
x_591 = l_Lean_Syntax_getArgs(x_2);
x_592 = lean_array_get_size(x_591);
x_593 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_594 = lean_unsigned_to_nat(0u);
x_595 = l_Array_findIdx_x3f_loop___rarg(x_591, x_593, x_592, x_594, lean_box(0));
lean_dec(x_591);
if (lean_obj_tag(x_595) == 0)
{
lean_dec(x_590);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_596; 
x_596 = !lean_is_exclusive(x_2);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; 
x_597 = lean_ctor_get(x_2, 1);
lean_dec(x_597);
x_598 = lean_ctor_get(x_2, 0);
lean_dec(x_598);
x_599 = lean_ctor_get(x_595, 0);
lean_inc(x_599);
lean_dec(x_595);
lean_inc(x_1);
x_600 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_600, 0, x_1);
lean_ctor_set(x_600, 1, x_1);
x_601 = lean_array_get_size(x_590);
x_602 = lean_nat_dec_lt(x_599, x_601);
lean_dec(x_601);
if (x_602 == 0)
{
lean_dec(x_600);
lean_dec(x_599);
return x_2;
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_603 = lean_array_fget(x_590, x_599);
x_604 = lean_box(0);
x_605 = lean_array_fset(x_590, x_599, x_604);
x_606 = l_Lean_Syntax_setInfo(x_600, x_603);
x_607 = lean_array_fset(x_605, x_599, x_606);
lean_dec(x_599);
lean_ctor_set(x_2, 1, x_607);
return x_2;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; uint8_t x_611; 
lean_dec(x_2);
x_608 = lean_ctor_get(x_595, 0);
lean_inc(x_608);
lean_dec(x_595);
lean_inc(x_1);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_1);
lean_ctor_set(x_609, 1, x_1);
x_610 = lean_array_get_size(x_590);
x_611 = lean_nat_dec_lt(x_608, x_610);
lean_dec(x_610);
if (x_611 == 0)
{
lean_object* x_612; 
lean_dec(x_609);
lean_dec(x_608);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_3);
lean_ctor_set(x_612, 1, x_590);
return x_612;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_613 = lean_array_fget(x_590, x_608);
x_614 = lean_box(0);
x_615 = lean_array_fset(x_590, x_608, x_614);
x_616 = l_Lean_Syntax_setInfo(x_609, x_613);
x_617 = lean_array_fset(x_615, x_608, x_616);
lean_dec(x_608);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_3);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
}
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_5);
lean_dec(x_4);
x_619 = lean_ctor_get(x_2, 1);
lean_inc(x_619);
x_620 = l_Lean_Syntax_getArgs(x_2);
x_621 = lean_array_get_size(x_620);
x_622 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_623 = lean_unsigned_to_nat(0u);
x_624 = l_Array_findIdx_x3f_loop___rarg(x_620, x_622, x_621, x_623, lean_box(0));
lean_dec(x_620);
if (lean_obj_tag(x_624) == 0)
{
lean_dec(x_619);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_625; 
x_625 = !lean_is_exclusive(x_2);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
x_626 = lean_ctor_get(x_2, 1);
lean_dec(x_626);
x_627 = lean_ctor_get(x_2, 0);
lean_dec(x_627);
x_628 = lean_ctor_get(x_624, 0);
lean_inc(x_628);
lean_dec(x_624);
lean_inc(x_1);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_1);
lean_ctor_set(x_629, 1, x_1);
x_630 = lean_array_get_size(x_619);
x_631 = lean_nat_dec_lt(x_628, x_630);
lean_dec(x_630);
if (x_631 == 0)
{
lean_dec(x_629);
lean_dec(x_628);
return x_2;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_632 = lean_array_fget(x_619, x_628);
x_633 = lean_box(0);
x_634 = lean_array_fset(x_619, x_628, x_633);
x_635 = l_Lean_Syntax_setInfo(x_629, x_632);
x_636 = lean_array_fset(x_634, x_628, x_635);
lean_dec(x_628);
lean_ctor_set(x_2, 1, x_636);
return x_2;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; uint8_t x_640; 
lean_dec(x_2);
x_637 = lean_ctor_get(x_624, 0);
lean_inc(x_637);
lean_dec(x_624);
lean_inc(x_1);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_1);
lean_ctor_set(x_638, 1, x_1);
x_639 = lean_array_get_size(x_619);
x_640 = lean_nat_dec_lt(x_637, x_639);
lean_dec(x_639);
if (x_640 == 0)
{
lean_object* x_641; 
lean_dec(x_638);
lean_dec(x_637);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_3);
lean_ctor_set(x_641, 1, x_619);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_642 = lean_array_fget(x_619, x_637);
x_643 = lean_box(0);
x_644 = lean_array_fset(x_619, x_637, x_643);
x_645 = l_Lean_Syntax_setInfo(x_638, x_642);
x_646 = lean_array_fset(x_644, x_637, x_645);
lean_dec(x_637);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_3);
lean_ctor_set(x_647, 1, x_646);
return x_647;
}
}
}
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_4);
x_648 = lean_ctor_get(x_2, 1);
lean_inc(x_648);
x_649 = l_Lean_Syntax_getArgs(x_2);
x_650 = lean_array_get_size(x_649);
x_651 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_652 = lean_unsigned_to_nat(0u);
x_653 = l_Array_findIdx_x3f_loop___rarg(x_649, x_651, x_650, x_652, lean_box(0));
lean_dec(x_649);
if (lean_obj_tag(x_653) == 0)
{
lean_dec(x_648);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_654; 
x_654 = !lean_is_exclusive(x_2);
if (x_654 == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; uint8_t x_660; 
x_655 = lean_ctor_get(x_2, 1);
lean_dec(x_655);
x_656 = lean_ctor_get(x_2, 0);
lean_dec(x_656);
x_657 = lean_ctor_get(x_653, 0);
lean_inc(x_657);
lean_dec(x_653);
lean_inc(x_1);
x_658 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_658, 0, x_1);
lean_ctor_set(x_658, 1, x_1);
x_659 = lean_array_get_size(x_648);
x_660 = lean_nat_dec_lt(x_657, x_659);
lean_dec(x_659);
if (x_660 == 0)
{
lean_dec(x_658);
lean_dec(x_657);
return x_2;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_661 = lean_array_fget(x_648, x_657);
x_662 = lean_box(0);
x_663 = lean_array_fset(x_648, x_657, x_662);
x_664 = l_Lean_Syntax_setInfo(x_658, x_661);
x_665 = lean_array_fset(x_663, x_657, x_664);
lean_dec(x_657);
lean_ctor_set(x_2, 1, x_665);
return x_2;
}
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
lean_dec(x_2);
x_666 = lean_ctor_get(x_653, 0);
lean_inc(x_666);
lean_dec(x_653);
lean_inc(x_1);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_1);
lean_ctor_set(x_667, 1, x_1);
x_668 = lean_array_get_size(x_648);
x_669 = lean_nat_dec_lt(x_666, x_668);
lean_dec(x_668);
if (x_669 == 0)
{
lean_object* x_670; 
lean_dec(x_667);
lean_dec(x_666);
x_670 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_670, 0, x_3);
lean_ctor_set(x_670, 1, x_648);
return x_670;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_671 = lean_array_fget(x_648, x_666);
x_672 = lean_box(0);
x_673 = lean_array_fset(x_648, x_666, x_672);
x_674 = l_Lean_Syntax_setInfo(x_667, x_671);
x_675 = lean_array_fset(x_673, x_666, x_674);
lean_dec(x_666);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_3);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
}
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_677 = lean_ctor_get(x_2, 1);
lean_inc(x_677);
x_678 = l_Lean_Syntax_getArgs(x_2);
x_679 = lean_array_get_size(x_678);
x_680 = l_Lean_PrettyPrinter_Delaborator_annotatePos___closed__1;
x_681 = lean_unsigned_to_nat(0u);
x_682 = l_Array_findIdx_x3f_loop___rarg(x_678, x_680, x_679, x_681, lean_box(0));
lean_dec(x_678);
if (lean_obj_tag(x_682) == 0)
{
lean_dec(x_677);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_683; 
x_683 = !lean_is_exclusive(x_2);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; uint8_t x_689; 
x_684 = lean_ctor_get(x_2, 1);
lean_dec(x_684);
x_685 = lean_ctor_get(x_2, 0);
lean_dec(x_685);
x_686 = lean_ctor_get(x_682, 0);
lean_inc(x_686);
lean_dec(x_682);
lean_inc(x_1);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_1);
lean_ctor_set(x_687, 1, x_1);
x_688 = lean_array_get_size(x_677);
x_689 = lean_nat_dec_lt(x_686, x_688);
lean_dec(x_688);
if (x_689 == 0)
{
lean_dec(x_687);
lean_dec(x_686);
return x_2;
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_690 = lean_array_fget(x_677, x_686);
x_691 = lean_box(0);
x_692 = lean_array_fset(x_677, x_686, x_691);
x_693 = l_Lean_Syntax_setInfo(x_687, x_690);
x_694 = lean_array_fset(x_692, x_686, x_693);
lean_dec(x_686);
lean_ctor_set(x_2, 1, x_694);
return x_2;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint8_t x_698; 
lean_dec(x_2);
x_695 = lean_ctor_get(x_682, 0);
lean_inc(x_695);
lean_dec(x_682);
lean_inc(x_1);
x_696 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_696, 0, x_1);
lean_ctor_set(x_696, 1, x_1);
x_697 = lean_array_get_size(x_677);
x_698 = lean_nat_dec_lt(x_695, x_697);
lean_dec(x_697);
if (x_698 == 0)
{
lean_object* x_699; 
lean_dec(x_696);
lean_dec(x_695);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_3);
lean_ctor_set(x_699, 1, x_677);
return x_699;
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
x_700 = lean_array_fget(x_677, x_695);
x_701 = lean_box(0);
x_702 = lean_array_fset(x_677, x_695, x_701);
x_703 = l_Lean_Syntax_setInfo(x_696, x_700);
x_704 = lean_array_fset(x_702, x_695, x_703);
lean_dec(x_695);
x_705 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_705, 0, x_3);
lean_ctor_set(x_705, 1, x_704);
return x_705;
}
}
}
}
}
case 3:
{
lean_object* x_706; lean_object* x_707; 
lean_inc(x_1);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_1);
lean_ctor_set(x_706, 1, x_1);
x_707 = l_Lean_Syntax_setInfo(x_706, x_2);
return x_707;
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
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_local_ctx_find(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_LocalDecl_userName(x_7);
lean_dec(x_7);
x_9 = lean_name_eq(x_8, x_2);
lean_dec(x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
}
}
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = 8192;
x_6 = l_Lean_Expr_FindImpl_initCache;
x_7 = l_Lean_Expr_FindImpl_findM_x3f_visit(x_4, x_5, x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = 1;
return x_10;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPSafeShadowing___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_936____closed__4;
x_2 = lean_erase_macro_scopes(x_1);
return x_2;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Lean_Name_isAnonymous(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_erase_macro_scopes(x_1);
lean_inc(x_11);
lean_inc(x_10);
x_12 = lean_local_ctx_uses_user_name(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
x_15 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_local_ctx_get_unused_name(x_10, x_11);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_local_ctx_get_unused_name(x_10, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
x_26 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_10, x_11);
if (x_26 == 0)
{
lean_dec(x_10);
lean_ctor_set(x_15, 0, x_11);
return x_15;
}
else
{
lean_object* x_27; 
x_27 = lean_local_ctx_get_unused_name(x_10, x_11);
lean_ctor_set(x_15, 0, x_27);
return x_15;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_10, x_11);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_10);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_local_ctx_get_unused_name(x_10, x_11);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
x_34 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2;
lean_inc(x_33);
x_35 = lean_local_ctx_uses_user_name(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_8);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
x_38 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_37, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_38);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_38, 0);
lean_dec(x_42);
x_43 = lean_local_ctx_get_unused_name(x_33, x_34);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = lean_local_ctx_get_unused_name(x_33, x_34);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_38, 0);
lean_dec(x_48);
lean_inc(x_33);
x_49 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_33, x_34);
if (x_49 == 0)
{
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_34);
return x_38;
}
else
{
lean_object* x_50; 
x_50 = lean_local_ctx_get_unused_name(x_33, x_34);
lean_ctor_set(x_38, 0, x_50);
return x_38;
}
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_38, 1);
lean_inc(x_51);
lean_dec(x_38);
lean_inc(x_33);
x_52 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_33, x_34);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_33);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_34);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_local_ctx_get_unused_name(x_33, x_34);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
}
}
}
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_getUnusedName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PrettyPrinter_Delaborator_getExpr(x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_bindingName_x21(x_9);
lean_dec(x_9);
x_15 = l_Lean_Expr_bindingBody_x21(x_12);
lean_dec(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_Lean_PrettyPrinter_Delaborator_getUnusedName(x_14, x_15, x_2, x_3, x_4, x_5, x_6, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = lean_mk_syntax_ident(x_17);
lean_inc(x_2);
x_20 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_19, x_2, x_3, x_4, x_5, x_6, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_apply_1(x_1, x_21);
x_24 = l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(x_17, x_23, x_2, x_3, x_4, x_5, x_6, x_22);
return x_24;
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
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_ScopedEnvExtension_getState___at_Lean_KeyedDeclsAttribute_getValues___spec__1___rarg___closed__1;
x_7 = l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
x_8 = lean_panic_fn(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_17 = x_2 >> x_5 % (sizeof(size_t) * 8);
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(x_4, x_2);
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_15 = l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(x_14, x_12);
lean_dec(x_12);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(x_16, x_1);
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
x_35 = l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__8(x_34, x_2, x_3, x_4, x_5, x_6, x_11);
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
lean_object* l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ScopedEnvExtension_getState___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(x_1, x_2);
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
x_1 = l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
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
x_5 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
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
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
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
x_3 = lean_unsigned_to_nat(387u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Formatter_categoryParser_formatter___lambda__2___closed__4;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_delab___closed__3;
x_2 = l_Lean_PrettyPrinter_format___closed__3;
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
x_58 = l_Lean_PrettyPrinter_delab___closed__4;
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
x_26 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
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
x_35 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax___closed__1;
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
x_42 = l_Std_fmt___at_Lean_ppExpr___spec__3(x_3);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_KernelException_toMessageData___closed__15;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Lean_PrettyPrinter_delab___closed__4;
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
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2123_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_delab___closed__3;
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
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_all = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_all);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_notation = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_notation);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_coercions = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_coercions);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_universes = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_universes);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_full__names = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_full__names);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_private__names = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_private__names);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_binder__types = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_binder__types);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__4);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__6);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_structure__instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_structure__instances);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_structure__projections = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_structure__projections);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_explicit = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_explicit);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_structure__instance__type = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_structure__instance__type);
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__3);
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__4);
res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_pp_safe__shadowing = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_pp_safe__shadowing);
lean_dec_ref(res);
l_Lean_getPPUnicode___closed__1 = _init_l_Lean_getPPUnicode___closed__1();
lean_mark_persistent(l_Lean_getPPUnicode___closed__1);
l_Lean_PrettyPrinter_Delaborator_Context_pos___default = _init_l_Lean_PrettyPrinter_Delaborator_Context_pos___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_Context_pos___default);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__1);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487____closed__2);
res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_487_(lean_io_mk_world());
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
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5);
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
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2);
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
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2123_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
