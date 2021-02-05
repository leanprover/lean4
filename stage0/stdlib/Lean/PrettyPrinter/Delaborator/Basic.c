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
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2(lean_object*, lean_object*, lean_object*, size_t, size_t, size_t, size_t);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__1(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__2;
lean_object* l_Lean_PrettyPrinter_delab___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__1;
lean_object* l_Lean_Syntax_modifyArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__8;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__1;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__1;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_getPPCoercions(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5;
lean_object* l_Lean_Syntax_isAtom___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_933____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPExplicit(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPNotation___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_descend(lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBody___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__8;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1;
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491_(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__4;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_271____closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__1;
uint8_t l_Lean_getPPStructureProjections(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_getPPOption___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_getPPSafeShadowing(lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPFullNames___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Init_NotationExtra___hyg_1133____closed__26;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj_match__1(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__2;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__2;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__3;
uint8_t l_Lean_getPPUniverses(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__3(lean_object*, size_t, lean_object*);
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
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__5;
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_autoBoundImplicitLocal___closed__1;
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
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_36____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__2(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__2(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__2;
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr___rarg___closed__1;
lean_object* l_Lean_pp_private__names;
lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object*);
uint8_t l_Lean_getPPPrivateNames(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_pp_structure__instance__type;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedKeyedDeclsAttribute___closed__1;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_4____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_descend___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_mkFormatterAttribute___closed__6;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_210____closed__3;
uint8_t l_Lean_getPPStructureInstances(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_5925____closed__20;
lean_object* l_Lean_pp_full__names;
extern lean_object* l_Lean_PrettyPrinter_format___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn(lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_withProj(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pp_explicit;
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_instMonadQuotationParenthesizerM___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_setPPExplicit___closed__1;
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6___boxed(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_synthInstance_x3f___lambda__2___closed__4;
lean_object* l_Lean_getPPCoercions___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFn___rarg___closed__4;
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_152____closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ctorName___closed__9;
uint8_t l_Lean_getPPNotation(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__3(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_FindImpl_initCache;
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureInstanceType___boxed(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__2;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__3;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_329____closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
extern lean_object* l_Lean_Parser_Command_notation___elambda__1___closed__1;
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
lean_object* l_Std_fmt___at_Lean_ppExpr___spec__2(lean_object*);
lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__2;
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Meta_ForEachExpr_0__Lean_Meta_ForEachExpr_visitBinder___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_getSanitizeNames___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2(lean_object*);
lean_object* l_Lean_getPPAll___boxed(lean_object*);
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPStructureInstances___boxed(lean_object*);
lean_object* l_Lean_getPPUniverses___boxed(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__4;
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
extern lean_object* l_Lean_Parser_Command_universes___elambda__1___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2;
lean_object* l_Lean_getPPExplicit___boxed(lean_object*);
lean_object* l_Lean_pp_structure__instances;
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_65____closed__2;
extern lean_object* l_Std_Format_getUnicode___closed__1;
lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__3;
lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object*);
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
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2116_(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_300____closed__4;
lean_object* lean_mk_syntax_ident(lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_242____closed__1;
extern lean_object* l_Lean_Elab_Term_instMonadQuotationTermElabM___closed__2;
lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBody(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_delab___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppArg___rarg___closed__1;
lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withAppFnArgs_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_getRoot(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_123____closed__3;
uint8_t l_Lean_getPPAll(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_withMDataExpr_match__1(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object*, lean_object*);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getSanitizeNames___closed__2;
x_2 = l_Lean_Parser_Command_universes___elambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(pretty printer) display universes");
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_getSanitizeNames___closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__2;
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
x_2 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1;
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3;
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_getPPAll(x_1);
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_181____closed__2;
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
x_3 = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__1;
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("delabFailure");
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2;
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
x_2 = l_Lean_myMacro____x40_Init_NotationExtra___hyg_1133____closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
x_2 = l___private_Init_Meta_0__Lean_Meta_Simp_reprConfig____x40_Init_Meta___hyg_5925____closed__20;
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
x_38 = l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
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
x_46 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
x_70 = l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
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
x_76 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
x_102 = l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
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
x_109 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
x_140 = l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
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
x_148 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
x_184 = l_myMacro____x40_Init_Notation___hyg_2191____closed__1;
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
x_193 = l_myMacro____x40_Init_Notation___hyg_2191____closed__3;
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
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Lean_Syntax_setInfo(x_7, x_2);
return x_8;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, size_t x_6, size_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_modifyArg(x_2, x_9, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Syntax_isAtom___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Syntax_getArgs(x_2);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_findIdx_x3f_loop___rarg(x_3, x_5, x_4, x_6, lean_box(0));
lean_dec(x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Syntax_setInfo), 2, 1);
lean_closure_set(x_10, 0, x_9);
x_11 = l_Lean_Syntax_modifyArg(x_2, x_8, x_10);
lean_dec(x_8);
return x_11;
}
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1___boxed), 6, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2___boxed), 7, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_PrettyPrinter_Delaborator_annotatePos_match__2___rarg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__2(x_1, x_2, x_3, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
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
x_1 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_933____closed__4;
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
x_2 = l_Lean_PrettyPrinter_format___closed__4;
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
x_42 = l_Std_fmt___at_Lean_ppExpr___spec__2(x_3);
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
lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2116_(lean_object* x_1) {
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
l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3 = _init_l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_94____closed__3);
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
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__1);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491____closed__2);
res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_491_(lean_io_mk_world());
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
l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_annotatePos___lambda__3___closed__1);
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
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2116_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
