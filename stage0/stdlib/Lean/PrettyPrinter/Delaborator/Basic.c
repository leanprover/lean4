// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Basic
// Imports: Init Lean.KeyedDeclsAttribute Lean.ProjFns Lean.Syntax Lean.Meta.Transform Lean.Meta.Match.Match Lean.Elab.Term Lean.Elab.AuxDiscr Lean.PrettyPrinter.Delaborator.Options Lean.PrettyPrinter.Delaborator.SubExpr Lean.PrettyPrinter.Delaborator.TopDownAnalyze
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
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__1;
uint8_t lean_local_ctx_uses_user_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFailureId;
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14;
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_SubExpr_Pos_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_get_unused_name(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_delab___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1;
lean_object* l_Lean_SourceInfo_fromRef(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18;
static lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4;
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_delabCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12;
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2;
lean_object* l_Lean_getPPAnalyzeTypeAscriptions___boxed(lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__7;
extern lean_object* l_Lean_pp_proofs;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
lean_object* l_Lean_Expr_FindImpl_findUnsafe_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_object*);
lean_object* l_ReaderT_instMonadLiftReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
lean_object* l_Std_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getPPAnalysisNeedsType___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15;
static lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object*);
lean_object* l_ReaderT_instMonadFunctorReaderT___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1;
lean_object* l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabAttribute;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_getPPProofs___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4;
lean_object* l_Lean_getPPProofsWithType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
uint8_t l_Lean_Name_isAtomic(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__9;
lean_object* l_Lean_Meta_erasePatternRefAnnotations___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
extern lean_object* l_Lean_Meta_instAlternativeMetaM;
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_checkMaxHeartbeats(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadQuotationCoreM;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3;
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
uint8_t l_Lean_getPPAnalyze(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16;
lean_object* l_Lean_resolveGlobalConstCore___at_Lean_registerInitAttrUnsafe___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__2;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2;
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_maxChildren;
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_Context_inPattern___default;
uint8_t l_Std_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13;
static lean_object* l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6;
lean_object* l_Lean_getPPSafeShadowing___boxed(lean_object*);
uint8_t l_Lean_Options_getInPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14;
lean_object* l_Lean_instMonadQuotation___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
uint8_t l_Lean_getPPInstantiateMVars(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2;
static lean_object* l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_State_infos___default;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20;
static lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___closed__4;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM;
static lean_object* l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22;
uint8_t l_Lean_Expr_binderInfo(lean_object*);
uint8_t l_Lean_Expr_isAtomic(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2;
lean_object* l_Lean_Meta_eraseInaccessibleAnnotations___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8;
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__3;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2830_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__5;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1(lean_object*);
static lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1;
lean_object* lean_mk_syntax_ident(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2(lean_object*, lean_object*);
lean_object* lean_local_ctx_find(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_init___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(lean_object*);
lean_object* l_Lean_Name_getRoot(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getPPAll(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_typeCoord;
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1;
lean_object* l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2(lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17;
uint8_t l_Lean_isAuxFunDiscrName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_State_holeIter___default;
static lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5;
static lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3;
lean_object* l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverloadCore___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instAlternativeReaderT___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_delabCore___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Attribute_Builtin_getId(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t _init_l_Lean_PrettyPrinter_Delaborator_Context_inPattern___default() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_State_infos___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_SubExpr_Pos_maxChildren;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_State_holeIter___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("delabFailure", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed), 8, 1);
lean_closure_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delabFailureId;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_2);
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
x_20 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
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
lean_dec(x_2);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_free_object(x_10);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = lean_apply_8(x_2, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
x_26 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_27 = lean_nat_dec_eq(x_26, x_25);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = lean_apply_8(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_orElse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_orElse___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_failure___rarg), 1, 0);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_failure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_failure(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_apply_7(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_21 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_22 = lean_nat_dec_eq(x_21, x_20);
lean_dec(x_20);
if (x_22 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_11);
lean_dec(x_12);
x_23 = lean_box(0);
x_24 = lean_apply_8(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_ctor_get(x_12, 0);
lean_inc(x_26);
x_27 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_12);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_12);
x_30 = lean_box(0);
x_31 = lean_apply_8(x_3, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_31;
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instAlternativeMetaM;
x_2 = l_Lean_Meta_instMonadMetaM;
x_3 = l_ReaderT_instAlternativeReaderT___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
x_3 = l_ReaderT_instAlternativeReaderT___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__2), 10, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 2);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4;
x_6 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5;
lean_ctor_set(x_1, 2, x_6);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4;
x_9 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5;
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_orElse___rarg), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1;
return x_2;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_apply_1(x_1, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_apply_1(x_1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2___rarg), 9, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 4);
lean_inc(x_2);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_ReaderT_read___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 4);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_3, 4, x_12);
x_13 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
x_17 = lean_ctor_get(x_3, 3);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*5);
x_19 = lean_ctor_get(x_3, 4);
lean_inc(x_19);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_20 = lean_apply_1(x_1, x_19);
x_21 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_17);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*5, x_18);
x_22 = lean_apply_7(x_2, x_21, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadWithReaderOfSubExprDelabM___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_1);
x_16 = lean_st_ref_set(x_3, x_12, x_13);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_12, 0);
lean_inc(x_23);
lean_dec(x_12);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
x_25 = lean_st_ref_set(x_3, x_24, x_13);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_27;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_apply_1(x_2, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_13, 1, x_19);
x_20 = lean_st_ref_set(x_4, x_13, x_14);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_apply_1(x_2, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_st_ref_set(x_4, x_30, x_14);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_map___at_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___spec__2___rarg), 9, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3___boxed), 8, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4___boxed), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_instMonadLiftReaderT), 3, 2);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_StateRefT_x27_lift), 4, 3);
lean_closure_set(x_1, 0, lean_box(0));
lean_closure_set(x_1, 1, lean_box(0));
lean_closure_set(x_1, 2, lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__5;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = lean_alloc_closure((void*)(l_ReaderT_instMonadFunctorReaderT___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
x_3 = l_Lean_Core_instMonadQuotationCoreM;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__3;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__4;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__1;
x_2 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10;
x_4 = l_Lean_instMonadQuotation___rarg(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___lambda__1), 9, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11;
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 3);
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 8, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 8, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12;
lean_ctor_set(x_1, 3, x_10);
lean_ctor_set(x_1, 2, x_9);
lean_ctor_set(x_1, 1, x_7);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 8, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_closure((void*)(l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed), 8, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12;
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_ReaderT_pure___at_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("builtinDelab", 12);
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
x_1 = lean_mk_string_from_bytes("delab", 5);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("PrettyPrinter", 13);
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
x_1 = lean_mk_string_from_bytes("Delaborator", 11);
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
x_1 = lean_mk_string_from_bytes("Delab", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Register a delaborator.\n\n  [delab k] registers a declaration of type `Lean.PrettyPrinter.Delaborator.Delab` for the `Lean.Expr`\n  constructor `k`. Multiple delaborators for a single constructor are tried in turn until\n  the first success. If the term to be delaborated is an application of a constant `c`,\n  elaborators for `app.c` are tried first; this is also done for `Expr.const`s (\"nullary applications\")\n  to reduce special casing. If the term is an `Expr.mdata` with a single key `k`, `mdata.k`\n  is tried first.", 519);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__2;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__4;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__13;
x_4 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__12;
x_5 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__14;
x_6 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15;
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("delabAttribute", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___lambda__2(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("bvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("fvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mvar", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sort", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("app", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lam", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("forallE", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("letE", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lit", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("mdata", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("proj", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_10; 
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__2;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
case 1:
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_8, 0);
lean_dec(x_17);
x_18 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
lean_ctor_set(x_8, 0, x_18);
return x_8;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__4;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
case 2:
{
uint8_t x_22; 
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_8, 0);
lean_dec(x_23);
x_24 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
lean_ctor_set(x_8, 0, x_24);
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 1);
lean_inc(x_25);
lean_dec(x_8);
x_26 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__6;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
case 3:
{
uint8_t x_28; 
lean_dec(x_9);
x_28 = !lean_is_exclusive(x_8);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_8, 0);
lean_dec(x_29);
x_30 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
lean_ctor_set(x_8, 0, x_30);
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__8;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
case 4:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_8);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_8, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_9, 0);
lean_inc(x_36);
lean_dec(x_9);
x_37 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_38 = l_Lean_Name_append(x_37, x_36);
lean_ctor_set(x_8, 0, x_38);
return x_8;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_8, 1);
lean_inc(x_39);
lean_dec(x_8);
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
x_41 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_42 = l_Lean_Name_append(x_41, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
case 5:
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
lean_dec(x_45);
x_46 = lean_ctor_get(x_9, 0);
lean_inc(x_46);
lean_dec(x_9);
x_47 = l_Lean_Expr_getAppFn(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_50 = l_Lean_Name_append(x_49, x_48);
lean_ctor_set(x_8, 0, x_50);
return x_8;
}
else
{
lean_object* x_51; 
lean_dec(x_47);
x_51 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_8, 1);
lean_inc(x_52);
lean_dec(x_8);
x_53 = lean_ctor_get(x_9, 0);
lean_inc(x_53);
lean_dec(x_9);
x_54 = l_Lean_Expr_getAppFn(x_53);
lean_dec(x_53);
if (lean_obj_tag(x_54) == 4)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_57 = l_Lean_Name_append(x_56, x_55);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_52);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
x_59 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__10;
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
return x_60;
}
}
}
case 6:
{
uint8_t x_61; 
lean_dec(x_9);
x_61 = !lean_is_exclusive(x_8);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_8, 0);
lean_dec(x_62);
x_63 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12;
lean_ctor_set(x_8, 0, x_63);
return x_8;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_8, 1);
lean_inc(x_64);
lean_dec(x_8);
x_65 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12;
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
case 7:
{
uint8_t x_67; 
lean_dec(x_9);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_8, 0);
lean_dec(x_68);
x_69 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14;
lean_ctor_set(x_8, 0, x_69);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_8, 1);
lean_inc(x_70);
lean_dec(x_8);
x_71 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
case 8:
{
uint8_t x_73; 
lean_dec(x_9);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_8, 0);
lean_dec(x_74);
x_75 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16;
lean_ctor_set(x_8, 0, x_75);
return x_8;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
lean_dec(x_8);
x_77 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16;
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
case 9:
{
uint8_t x_79; 
lean_dec(x_9);
x_79 = !lean_is_exclusive(x_8);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_8, 0);
lean_dec(x_80);
x_81 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18;
lean_ctor_set(x_8, 0, x_81);
return x_8;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_8, 1);
lean_inc(x_82);
lean_dec(x_8);
x_83 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
case 10:
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_9, 0);
lean_inc(x_85);
lean_dec(x_9);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_8);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_8, 0);
lean_dec(x_87);
x_88 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
lean_ctor_set(x_8, 0, x_88);
return x_8;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_8, 1);
lean_inc(x_89);
lean_dec(x_8);
x_90 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_dec(x_85);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_8);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_8, 0);
lean_dec(x_95);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
x_97 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
x_98 = l_Lean_Name_append(x_97, x_96);
lean_ctor_set(x_8, 0, x_98);
return x_8;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_8, 1);
lean_inc(x_99);
lean_dec(x_8);
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
lean_dec(x_92);
x_101 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
x_102 = l_Lean_Name_append(x_101, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_93);
lean_dec(x_92);
x_104 = !lean_is_exclusive(x_8);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_8, 0);
lean_dec(x_105);
x_106 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
lean_ctor_set(x_8, 0, x_106);
return x_8;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_8, 1);
lean_inc(x_107);
lean_dec(x_8);
x_108 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
default: 
{
uint8_t x_110; 
lean_dec(x_9);
x_110 = !lean_is_exclusive(x_8);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_8, 0);
lean_dec(x_111);
x_112 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22;
lean_ctor_set(x_8, 0, x_112);
return x_8;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_8, 1);
lean_inc(x_113);
lean_dec(x_8);
x_114 = l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getExprKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_getExprKind(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 4);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_KVMap_insertCore(x_2, x_13, x_14);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1;
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(x_13, x_10);
lean_dec(x_10);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_apply_9(x_12, x_8, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2(x_17, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = lean_apply_9(x_12, x_19, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_20);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_loop___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_apply_1(x_1, x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_apply_1(x_1, x_15);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_16);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_whenNotPPOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(x_15, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = l_Lean_KVMap_insertCore(x_17, x_1, x_2);
x_19 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_15, x_12, x_18);
lean_ctor_set(x_4, 1, x_19);
x_20 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_KVMap_insertCore(x_21, x_1, x_2);
x_23 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_15, x_12, x_22);
lean_ctor_set(x_4, 1, x_23);
x_24 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
x_27 = lean_ctor_get(x_4, 2);
x_28 = lean_ctor_get(x_4, 3);
x_29 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_30 = lean_ctor_get(x_4, 4);
lean_inc(x_30);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_31 = l_Std_RBNode_find___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__5(x_26, x_12);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_box(0);
x_33 = l_Lean_KVMap_insertCore(x_32, x_1, x_2);
x_34 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_26, x_12, x_33);
x_35 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_27);
lean_ctor_set(x_35, 3, x_28);
lean_ctor_set(x_35, 4, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*5, x_29);
x_36 = lean_apply_7(x_3, x_35, x_5, x_6, x_7, x_8, x_9, x_13);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
lean_dec(x_31);
x_38 = l_Lean_KVMap_insertCore(x_37, x_1, x_2);
x_39 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_TopDownAnalyze_annotateBoolAt___spec__1(x_26, x_12, x_38);
x_40 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_30);
lean_ctor_set_uint8(x_40, sizeof(void*)*5, x_29);
x_41 = lean_apply_7(x_3, x_40, x_5, x_6, x_7, x_8, x_9, x_13);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withOptionAtCurrPos___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotatePos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
lean_inc(x_1);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
x_4 = l_Lean_Syntax_setInfo(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_11, x_1);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_PrettyPrinter_Delaborator_annotatePos(x_13, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_annotateCurPos___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT uint8_t l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_Expr_FindImpl_findUnsafe_x3f(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("x", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_getUnusedName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Name_isAnonymous(x_1);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
if (x_10 == 0)
{
x_12 = x_1;
goto block_66;
}
else
{
lean_object* x_67; 
lean_dec(x_1);
x_67 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5;
x_12 = x_67;
goto block_66;
}
block_66:
{
uint8_t x_13; 
lean_inc(x_12);
x_13 = l_Lean_isAuxFunDiscrName(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_erase_macro_scopes(x_12);
lean_inc(x_14);
lean_inc(x_11);
x_15 = lean_local_ctx_uses_user_name(x_11, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
x_18 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_local_ctx_get_unused_name(x_11, x_14);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_local_ctx_get_unused_name(x_11, x_14);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
lean_inc(x_14);
lean_inc(x_11);
x_29 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_11, x_14);
if (x_29 == 0)
{
lean_dec(x_11);
lean_ctor_set(x_18, 0, x_14);
return x_18;
}
else
{
lean_object* x_30; 
x_30 = lean_local_ctx_get_unused_name(x_11, x_14);
lean_ctor_set(x_18, 0, x_30);
return x_18;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
lean_inc(x_14);
lean_inc(x_11);
x_32 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_11, x_14);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_11);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_14);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_local_ctx_get_unused_name(x_11, x_14);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_12);
x_40 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3;
lean_inc(x_11);
x_41 = lean_local_ctx_uses_user_name(x_11, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_9);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1;
x_44 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
uint8_t x_47; 
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_44, 0);
lean_dec(x_48);
x_49 = lean_local_ctx_get_unused_name(x_11, x_40);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_local_ctx_get_unused_name(x_11, x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_44, 0);
lean_dec(x_54);
lean_inc(x_11);
x_55 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_11, x_40);
if (x_55 == 0)
{
lean_dec(x_11);
lean_ctor_set(x_44, 0, x_40);
return x_44;
}
else
{
lean_object* x_56; 
x_56 = lean_local_ctx_get_unused_name(x_11, x_40);
lean_ctor_set(x_44, 0, x_56);
return x_44;
}
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
lean_inc(x_11);
x_58 = l_Lean_PrettyPrinter_Delaborator_getUnusedName_bodyUsesSuggestion(x_2, x_11, x_40);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_11);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_40);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_local_ctx_get_unused_name(x_11, x_40);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_11);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
return x_44;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_44, 0);
x_64 = lean_ctor_get(x_44, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_44);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_SubExpr_Pos_push(x_13, x_2);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 4, x_15);
x_16 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_22 = lean_ctor_get(x_4, 4);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_SubExpr_Pos_push(x_23, x_2);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_21);
x_27 = lean_apply_7(x_3, x_26, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Expr_bindingBody_x21(x_1);
lean_dec(x_1);
x_12 = lean_expr_instantiate1(x_11, x_3);
lean_dec(x_3);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__2___rarg(x_12, x_13, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_binderInfo(x_11);
x_14 = l_Lean_Expr_bindingDomain_x21(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg___lambda__1), 10, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_2);
x_16 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg(x_1, x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_bindingName_x21(x_10);
lean_dec(x_10);
x_16 = l_Lean_Expr_bindingBody_x21(x_13);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_PrettyPrinter_Delaborator_getUnusedName(x_15, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = lean_mk_syntax_ident(x_18);
x_21 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_apply_1(x_1, x_22);
x_25 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__1___rarg(x_18, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_PrettyPrinter_Delaborator_withBindingBodyUnusedName___spec__3___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_5(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_PrettyPrinter_Delaborator_liftMetaM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_box(0);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
lean_ctor_set(x_15, 3, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*4, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_10);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = 0;
x_6 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get(x_1, 3);
x_13 = lean_nat_dec_lt(x_2, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_2, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_12, x_2, x_3);
x_16 = 0;
lean_ctor_set(x_1, 3, x_15);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
return x_1;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
x_17 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_17);
return x_1;
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_9, x_2, x_3);
x_19 = 0;
lean_ctor_set(x_1, 0, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_24 = lean_nat_dec_lt(x_2, x_21);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_eq(x_2, x_21);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_26 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_23, x_2, x_3);
x_27 = 0;
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_21);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
x_29 = 0;
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_20);
lean_ctor_set(x_30, 1, x_2);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_29);
return x_30;
}
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_20, x_2, x_3);
x_32 = 0;
x_33 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_22);
lean_ctor_set(x_33, 3, x_23);
lean_ctor_set_uint8(x_33, sizeof(void*)*4, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_1);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
x_39 = lean_nat_dec_lt(x_2, x_36);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_nat_dec_eq(x_2, x_36);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Std_RBNode_isRed___rarg(x_38);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_38, x_2, x_3);
x_43 = 1;
lean_ctor_set(x_1, 3, x_42);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_38, x_2, x_3);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 3);
lean_inc(x_46);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_44, 3);
lean_dec(x_48);
x_49 = lean_ctor_get(x_44, 0);
lean_dec(x_49);
x_50 = 0;
lean_ctor_set(x_44, 0, x_46);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_50);
x_51 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_51);
return x_1;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_44, 1);
x_53 = lean_ctor_get(x_44, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = 0;
x_55 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_46);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_54);
x_56 = 1;
lean_ctor_set(x_1, 3, x_55);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_46, sizeof(void*)*4);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_44);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_44, 1);
x_60 = lean_ctor_get(x_44, 2);
x_61 = lean_ctor_get(x_44, 3);
lean_dec(x_61);
x_62 = lean_ctor_get(x_44, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_46);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; 
x_64 = lean_ctor_get(x_46, 0);
x_65 = lean_ctor_get(x_46, 1);
x_66 = lean_ctor_get(x_46, 2);
x_67 = lean_ctor_get(x_46, 3);
x_68 = 1;
lean_ctor_set(x_46, 3, x_45);
lean_ctor_set(x_46, 2, x_37);
lean_ctor_set(x_46, 1, x_36);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_68);
lean_ctor_set(x_44, 3, x_67);
lean_ctor_set(x_44, 2, x_66);
lean_ctor_set(x_44, 1, x_65);
lean_ctor_set(x_44, 0, x_64);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_68);
x_69 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_69);
return x_1;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_46, 0);
x_71 = lean_ctor_get(x_46, 1);
x_72 = lean_ctor_get(x_46, 2);
x_73 = lean_ctor_get(x_46, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_46);
x_74 = 1;
x_75 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_75, 0, x_35);
lean_ctor_set(x_75, 1, x_36);
lean_ctor_set(x_75, 2, x_37);
lean_ctor_set(x_75, 3, x_45);
lean_ctor_set_uint8(x_75, sizeof(void*)*4, x_74);
lean_ctor_set(x_44, 3, x_73);
lean_ctor_set(x_44, 2, x_72);
lean_ctor_set(x_44, 1, x_71);
lean_ctor_set(x_44, 0, x_70);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_74);
x_76 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_60);
lean_ctor_set(x_1, 1, x_59);
lean_ctor_set(x_1, 0, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_76);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_44, 1);
x_78 = lean_ctor_get(x_44, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_44);
x_79 = lean_ctor_get(x_46, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_46, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_46, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 lean_ctor_release(x_46, 3);
 x_83 = x_46;
} else {
 lean_dec_ref(x_46);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
lean_ctor_set(x_85, 2, x_37);
lean_ctor_set(x_85, 3, x_45);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
x_87 = 0;
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_44);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_44, 3);
lean_dec(x_89);
x_90 = lean_ctor_get(x_44, 0);
lean_dec(x_90);
x_91 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_91);
x_92 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_44, 1);
x_94 = lean_ctor_get(x_44, 2);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_44);
x_95 = 0;
x_96 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_96, 0, x_45);
lean_ctor_set(x_96, 1, x_93);
lean_ctor_set(x_96, 2, x_94);
lean_ctor_set(x_96, 3, x_46);
lean_ctor_set_uint8(x_96, sizeof(void*)*4, x_95);
x_97 = 1;
lean_ctor_set(x_1, 3, x_96);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_97);
return x_1;
}
}
}
}
else
{
uint8_t x_98; 
x_98 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_98 == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_44);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_44, 0);
lean_dec(x_100);
x_101 = !lean_is_exclusive(x_45);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_102 = lean_ctor_get(x_45, 0);
x_103 = lean_ctor_get(x_45, 1);
x_104 = lean_ctor_get(x_45, 2);
x_105 = lean_ctor_get(x_45, 3);
x_106 = 1;
lean_ctor_set(x_45, 3, x_102);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 0, x_35);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_106);
lean_ctor_set(x_44, 0, x_105);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_106);
x_107 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_104);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_107);
return x_1;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; uint8_t x_114; 
x_108 = lean_ctor_get(x_45, 0);
x_109 = lean_ctor_get(x_45, 1);
x_110 = lean_ctor_get(x_45, 2);
x_111 = lean_ctor_get(x_45, 3);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_45);
x_112 = 1;
x_113 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_113, 0, x_35);
lean_ctor_set(x_113, 1, x_36);
lean_ctor_set(x_113, 2, x_37);
lean_ctor_set(x_113, 3, x_108);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_112);
lean_ctor_set(x_44, 0, x_111);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_112);
x_114 = 0;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set(x_1, 2, x_110);
lean_ctor_set(x_1, 1, x_109);
lean_ctor_set(x_1, 0, x_113);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_114);
return x_1;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_115 = lean_ctor_get(x_44, 1);
x_116 = lean_ctor_get(x_44, 2);
x_117 = lean_ctor_get(x_44, 3);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_44);
x_118 = lean_ctor_get(x_45, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_45, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_45, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_45, 3);
lean_inc(x_121);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_122 = x_45;
} else {
 lean_dec_ref(x_45);
 x_122 = lean_box(0);
}
x_123 = 1;
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(1, 4, 1);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_35);
lean_ctor_set(x_124, 1, x_36);
lean_ctor_set(x_124, 2, x_37);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set_uint8(x_124, sizeof(void*)*4, x_123);
x_125 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_115);
lean_ctor_set(x_125, 2, x_116);
lean_ctor_set(x_125, 3, x_117);
lean_ctor_set_uint8(x_125, sizeof(void*)*4, x_123);
x_126 = 0;
lean_ctor_set(x_1, 3, x_125);
lean_ctor_set(x_1, 2, x_120);
lean_ctor_set(x_1, 1, x_119);
lean_ctor_set(x_1, 0, x_124);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_126);
return x_1;
}
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_44, 3);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
uint8_t x_128; 
x_128 = !lean_is_exclusive(x_44);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; 
x_129 = lean_ctor_get(x_44, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_44, 0);
lean_dec(x_130);
x_131 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_131);
x_132 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_132);
return x_1;
}
else
{
lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_44, 1);
x_134 = lean_ctor_get(x_44, 2);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_44);
x_135 = 0;
x_136 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_136, 0, x_45);
lean_ctor_set(x_136, 1, x_133);
lean_ctor_set(x_136, 2, x_134);
lean_ctor_set(x_136, 3, x_127);
lean_ctor_set_uint8(x_136, sizeof(void*)*4, x_135);
x_137 = 1;
lean_ctor_set(x_1, 3, x_136);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_137);
return x_1;
}
}
else
{
uint8_t x_138; 
x_138 = lean_ctor_get_uint8(x_127, sizeof(void*)*4);
if (x_138 == 0)
{
uint8_t x_139; 
lean_free_object(x_1);
x_139 = !lean_is_exclusive(x_44);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_140 = lean_ctor_get(x_44, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_44, 0);
lean_dec(x_141);
x_142 = !lean_is_exclusive(x_127);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_148; 
x_143 = lean_ctor_get(x_127, 0);
x_144 = lean_ctor_get(x_127, 1);
x_145 = lean_ctor_get(x_127, 2);
x_146 = lean_ctor_get(x_127, 3);
x_147 = 1;
lean_inc(x_45);
lean_ctor_set(x_127, 3, x_45);
lean_ctor_set(x_127, 2, x_37);
lean_ctor_set(x_127, 1, x_36);
lean_ctor_set(x_127, 0, x_35);
x_148 = !lean_is_exclusive(x_45);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_149 = lean_ctor_get(x_45, 3);
lean_dec(x_149);
x_150 = lean_ctor_get(x_45, 2);
lean_dec(x_150);
x_151 = lean_ctor_get(x_45, 1);
lean_dec(x_151);
x_152 = lean_ctor_get(x_45, 0);
lean_dec(x_152);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
lean_ctor_set(x_45, 3, x_146);
lean_ctor_set(x_45, 2, x_145);
lean_ctor_set(x_45, 1, x_144);
lean_ctor_set(x_45, 0, x_143);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_147);
x_153 = 0;
lean_ctor_set(x_44, 3, x_45);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_153);
return x_44;
}
else
{
lean_object* x_154; uint8_t x_155; 
lean_dec(x_45);
lean_ctor_set_uint8(x_127, sizeof(void*)*4, x_147);
x_154 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_154, 0, x_143);
lean_ctor_set(x_154, 1, x_144);
lean_ctor_set(x_154, 2, x_145);
lean_ctor_set(x_154, 3, x_146);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_147);
x_155 = 0;
lean_ctor_set(x_44, 3, x_154);
lean_ctor_set(x_44, 0, x_127);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_155);
return x_44;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_156 = lean_ctor_get(x_127, 0);
x_157 = lean_ctor_get(x_127, 1);
x_158 = lean_ctor_get(x_127, 2);
x_159 = lean_ctor_get(x_127, 3);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_127);
x_160 = 1;
lean_inc(x_45);
x_161 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_161, 0, x_35);
lean_ctor_set(x_161, 1, x_36);
lean_ctor_set(x_161, 2, x_37);
lean_ctor_set(x_161, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_162 = x_45;
} else {
 lean_dec_ref(x_45);
 x_162 = lean_box(0);
}
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_160);
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 4, 1);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_156);
lean_ctor_set(x_163, 1, x_157);
lean_ctor_set(x_163, 2, x_158);
lean_ctor_set(x_163, 3, x_159);
lean_ctor_set_uint8(x_163, sizeof(void*)*4, x_160);
x_164 = 0;
lean_ctor_set(x_44, 3, x_163);
lean_ctor_set(x_44, 0, x_161);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_164);
return x_44;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
x_165 = lean_ctor_get(x_44, 1);
x_166 = lean_ctor_get(x_44, 2);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_167 = lean_ctor_get(x_127, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_127, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_127, 2);
lean_inc(x_169);
x_170 = lean_ctor_get(x_127, 3);
lean_inc(x_170);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 lean_ctor_release(x_127, 2);
 lean_ctor_release(x_127, 3);
 x_171 = x_127;
} else {
 lean_dec_ref(x_127);
 x_171 = lean_box(0);
}
x_172 = 1;
lean_inc(x_45);
if (lean_is_scalar(x_171)) {
 x_173 = lean_alloc_ctor(1, 4, 1);
} else {
 x_173 = x_171;
}
lean_ctor_set(x_173, 0, x_35);
lean_ctor_set(x_173, 1, x_36);
lean_ctor_set(x_173, 2, x_37);
lean_ctor_set(x_173, 3, x_45);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_174 = x_45;
} else {
 lean_dec_ref(x_45);
 x_174 = lean_box(0);
}
lean_ctor_set_uint8(x_173, sizeof(void*)*4, x_172);
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 4, 1);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_167);
lean_ctor_set(x_175, 1, x_168);
lean_ctor_set(x_175, 2, x_169);
lean_ctor_set(x_175, 3, x_170);
lean_ctor_set_uint8(x_175, sizeof(void*)*4, x_172);
x_176 = 0;
x_177 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_177, 0, x_173);
lean_ctor_set(x_177, 1, x_165);
lean_ctor_set(x_177, 2, x_166);
lean_ctor_set(x_177, 3, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*4, x_176);
return x_177;
}
}
else
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_44);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = lean_ctor_get(x_44, 3);
lean_dec(x_179);
x_180 = lean_ctor_get(x_44, 0);
lean_dec(x_180);
x_181 = !lean_is_exclusive(x_45);
if (x_181 == 0)
{
uint8_t x_182; uint8_t x_183; 
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_138);
x_182 = 0;
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_182);
x_183 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_190; 
x_184 = lean_ctor_get(x_45, 0);
x_185 = lean_ctor_get(x_45, 1);
x_186 = lean_ctor_get(x_45, 2);
x_187 = lean_ctor_get(x_45, 3);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_45);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_186);
lean_ctor_set(x_188, 3, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_138);
x_189 = 0;
lean_ctor_set(x_44, 0, x_188);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_189);
x_190 = 1;
lean_ctor_set(x_1, 3, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_190);
return x_1;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; uint8_t x_201; 
x_191 = lean_ctor_get(x_44, 1);
x_192 = lean_ctor_get(x_44, 2);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_44);
x_193 = lean_ctor_get(x_45, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_45, 1);
lean_inc(x_194);
x_195 = lean_ctor_get(x_45, 2);
lean_inc(x_195);
x_196 = lean_ctor_get(x_45, 3);
lean_inc(x_196);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_197 = x_45;
} else {
 lean_dec_ref(x_45);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 4, 1);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_193);
lean_ctor_set(x_198, 1, x_194);
lean_ctor_set(x_198, 2, x_195);
lean_ctor_set(x_198, 3, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_138);
x_199 = 0;
x_200 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_191);
lean_ctor_set(x_200, 2, x_192);
lean_ctor_set(x_200, 3, x_127);
lean_ctor_set_uint8(x_200, sizeof(void*)*4, x_199);
x_201 = 1;
lean_ctor_set(x_1, 3, x_200);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_201);
return x_1;
}
}
}
}
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_37);
lean_dec(x_36);
x_202 = 1;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_202);
return x_1;
}
}
else
{
uint8_t x_203; 
x_203 = l_Std_RBNode_isRed___rarg(x_35);
if (x_203 == 0)
{
lean_object* x_204; uint8_t x_205; 
x_204 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_35, x_2, x_3);
x_205 = 1;
lean_ctor_set(x_1, 0, x_204);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_205);
return x_1;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_35, x_2, x_3);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_206, 3);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_206);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; uint8_t x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_206, 3);
lean_dec(x_210);
x_211 = lean_ctor_get(x_206, 0);
lean_dec(x_211);
x_212 = 0;
lean_ctor_set(x_206, 0, x_208);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_212);
x_213 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_213);
return x_1;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_206, 1);
x_215 = lean_ctor_get(x_206, 2);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_206);
x_216 = 0;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_208);
lean_ctor_set(x_217, 1, x_214);
lean_ctor_set(x_217, 2, x_215);
lean_ctor_set(x_217, 3, x_208);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
x_218 = 1;
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_218);
return x_1;
}
}
else
{
uint8_t x_219; 
x_219 = lean_ctor_get_uint8(x_208, sizeof(void*)*4);
if (x_219 == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_206);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_206, 1);
x_222 = lean_ctor_get(x_206, 2);
x_223 = lean_ctor_get(x_206, 3);
lean_dec(x_223);
x_224 = lean_ctor_get(x_206, 0);
lean_dec(x_224);
x_225 = !lean_is_exclusive(x_208);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; uint8_t x_231; 
x_226 = lean_ctor_get(x_208, 0);
x_227 = lean_ctor_get(x_208, 1);
x_228 = lean_ctor_get(x_208, 2);
x_229 = lean_ctor_get(x_208, 3);
x_230 = 1;
lean_ctor_set(x_208, 3, x_226);
lean_ctor_set(x_208, 2, x_222);
lean_ctor_set(x_208, 1, x_221);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set_uint8(x_208, sizeof(void*)*4, x_230);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_229);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_230);
x_231 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_228);
lean_ctor_set(x_1, 1, x_227);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_231);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_208, 0);
x_233 = lean_ctor_get(x_208, 1);
x_234 = lean_ctor_get(x_208, 2);
x_235 = lean_ctor_get(x_208, 3);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_208);
x_236 = 1;
x_237 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_237, 0, x_207);
lean_ctor_set(x_237, 1, x_221);
lean_ctor_set(x_237, 2, x_222);
lean_ctor_set(x_237, 3, x_232);
lean_ctor_set_uint8(x_237, sizeof(void*)*4, x_236);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_235);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_236);
x_238 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_234);
lean_ctor_set(x_1, 1, x_233);
lean_ctor_set(x_1, 0, x_237);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_238);
return x_1;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_239 = lean_ctor_get(x_206, 1);
x_240 = lean_ctor_get(x_206, 2);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_206);
x_241 = lean_ctor_get(x_208, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_208, 1);
lean_inc(x_242);
x_243 = lean_ctor_get(x_208, 2);
lean_inc(x_243);
x_244 = lean_ctor_get(x_208, 3);
lean_inc(x_244);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 lean_ctor_release(x_208, 2);
 lean_ctor_release(x_208, 3);
 x_245 = x_208;
} else {
 lean_dec_ref(x_208);
 x_245 = lean_box(0);
}
x_246 = 1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 4, 1);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_207);
lean_ctor_set(x_247, 1, x_239);
lean_ctor_set(x_247, 2, x_240);
lean_ctor_set(x_247, 3, x_241);
lean_ctor_set_uint8(x_247, sizeof(void*)*4, x_246);
x_248 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_248, 0, x_244);
lean_ctor_set(x_248, 1, x_36);
lean_ctor_set(x_248, 2, x_37);
lean_ctor_set(x_248, 3, x_38);
lean_ctor_set_uint8(x_248, sizeof(void*)*4, x_246);
x_249 = 0;
lean_ctor_set(x_1, 3, x_248);
lean_ctor_set(x_1, 2, x_243);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_247);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_249);
return x_1;
}
}
else
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_206);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; 
x_251 = lean_ctor_get(x_206, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_206, 0);
lean_dec(x_252);
x_253 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_253);
x_254 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_254);
return x_1;
}
else
{
lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_255 = lean_ctor_get(x_206, 1);
x_256 = lean_ctor_get(x_206, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_206);
x_257 = 0;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_207);
lean_ctor_set(x_258, 1, x_255);
lean_ctor_set(x_258, 2, x_256);
lean_ctor_set(x_258, 3, x_208);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
x_259 = 1;
lean_ctor_set(x_1, 0, x_258);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_259);
return x_1;
}
}
}
}
else
{
uint8_t x_260; 
x_260 = lean_ctor_get_uint8(x_207, sizeof(void*)*4);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_206);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_262 = lean_ctor_get(x_206, 1);
x_263 = lean_ctor_get(x_206, 2);
x_264 = lean_ctor_get(x_206, 3);
x_265 = lean_ctor_get(x_206, 0);
lean_dec(x_265);
x_266 = !lean_is_exclusive(x_207);
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; 
x_267 = 1;
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_267);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_267);
x_268 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_207);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_268);
return x_1;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_207, 0);
x_270 = lean_ctor_get(x_207, 1);
x_271 = lean_ctor_get(x_207, 2);
x_272 = lean_ctor_get(x_207, 3);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_207);
x_273 = 1;
x_274 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_270);
lean_ctor_set(x_274, 2, x_271);
lean_ctor_set(x_274, 3, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4, x_273);
lean_ctor_set(x_206, 3, x_38);
lean_ctor_set(x_206, 2, x_37);
lean_ctor_set(x_206, 1, x_36);
lean_ctor_set(x_206, 0, x_264);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_273);
x_275 = 0;
lean_ctor_set(x_1, 3, x_206);
lean_ctor_set(x_1, 2, x_263);
lean_ctor_set(x_1, 1, x_262);
lean_ctor_set(x_1, 0, x_274);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_275);
return x_1;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_276 = lean_ctor_get(x_206, 1);
x_277 = lean_ctor_get(x_206, 2);
x_278 = lean_ctor_get(x_206, 3);
lean_inc(x_278);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_206);
x_279 = lean_ctor_get(x_207, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_207, 1);
lean_inc(x_280);
x_281 = lean_ctor_get(x_207, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_207, 3);
lean_inc(x_282);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_283 = x_207;
} else {
 lean_dec_ref(x_207);
 x_283 = lean_box(0);
}
x_284 = 1;
if (lean_is_scalar(x_283)) {
 x_285 = lean_alloc_ctor(1, 4, 1);
} else {
 x_285 = x_283;
}
lean_ctor_set(x_285, 0, x_279);
lean_ctor_set(x_285, 1, x_280);
lean_ctor_set(x_285, 2, x_281);
lean_ctor_set(x_285, 3, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*4, x_284);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_278);
lean_ctor_set(x_286, 1, x_36);
lean_ctor_set(x_286, 2, x_37);
lean_ctor_set(x_286, 3, x_38);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_284);
x_287 = 0;
lean_ctor_set(x_1, 3, x_286);
lean_ctor_set(x_1, 2, x_277);
lean_ctor_set(x_1, 1, x_276);
lean_ctor_set(x_1, 0, x_285);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_287);
return x_1;
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_206, 3);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_206);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; uint8_t x_293; 
x_290 = lean_ctor_get(x_206, 3);
lean_dec(x_290);
x_291 = lean_ctor_get(x_206, 0);
lean_dec(x_291);
x_292 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_292);
x_293 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_293);
return x_1;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
x_294 = lean_ctor_get(x_206, 1);
x_295 = lean_ctor_get(x_206, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_206);
x_296 = 0;
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_207);
lean_ctor_set(x_297, 1, x_294);
lean_ctor_set(x_297, 2, x_295);
lean_ctor_set(x_297, 3, x_288);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_296);
x_298 = 1;
lean_ctor_set(x_1, 0, x_297);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_298);
return x_1;
}
}
else
{
uint8_t x_299; 
x_299 = lean_ctor_get_uint8(x_288, sizeof(void*)*4);
if (x_299 == 0)
{
uint8_t x_300; 
lean_free_object(x_1);
x_300 = !lean_is_exclusive(x_206);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_301 = lean_ctor_get(x_206, 1);
x_302 = lean_ctor_get(x_206, 2);
x_303 = lean_ctor_get(x_206, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_206, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_288);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; uint8_t x_311; 
x_306 = lean_ctor_get(x_288, 0);
x_307 = lean_ctor_get(x_288, 1);
x_308 = lean_ctor_get(x_288, 2);
x_309 = lean_ctor_get(x_288, 3);
x_310 = 1;
lean_inc(x_207);
lean_ctor_set(x_288, 3, x_306);
lean_ctor_set(x_288, 2, x_302);
lean_ctor_set(x_288, 1, x_301);
lean_ctor_set(x_288, 0, x_207);
x_311 = !lean_is_exclusive(x_207);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
x_312 = lean_ctor_get(x_207, 3);
lean_dec(x_312);
x_313 = lean_ctor_get(x_207, 2);
lean_dec(x_313);
x_314 = lean_ctor_get(x_207, 1);
lean_dec(x_314);
x_315 = lean_ctor_get(x_207, 0);
lean_dec(x_315);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
lean_ctor_set(x_207, 3, x_38);
lean_ctor_set(x_207, 2, x_37);
lean_ctor_set(x_207, 1, x_36);
lean_ctor_set(x_207, 0, x_309);
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_310);
x_316 = 0;
lean_ctor_set(x_206, 3, x_207);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_316);
return x_206;
}
else
{
lean_object* x_317; uint8_t x_318; 
lean_dec(x_207);
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_310);
x_317 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_317, 0, x_309);
lean_ctor_set(x_317, 1, x_36);
lean_ctor_set(x_317, 2, x_37);
lean_ctor_set(x_317, 3, x_38);
lean_ctor_set_uint8(x_317, sizeof(void*)*4, x_310);
x_318 = 0;
lean_ctor_set(x_206, 3, x_317);
lean_ctor_set(x_206, 2, x_308);
lean_ctor_set(x_206, 1, x_307);
lean_ctor_set(x_206, 0, x_288);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_318);
return x_206;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; 
x_319 = lean_ctor_get(x_288, 0);
x_320 = lean_ctor_get(x_288, 1);
x_321 = lean_ctor_get(x_288, 2);
x_322 = lean_ctor_get(x_288, 3);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_288);
x_323 = 1;
lean_inc(x_207);
x_324 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_324, 0, x_207);
lean_ctor_set(x_324, 1, x_301);
lean_ctor_set(x_324, 2, x_302);
lean_ctor_set(x_324, 3, x_319);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_325 = x_207;
} else {
 lean_dec_ref(x_207);
 x_325 = lean_box(0);
}
lean_ctor_set_uint8(x_324, sizeof(void*)*4, x_323);
if (lean_is_scalar(x_325)) {
 x_326 = lean_alloc_ctor(1, 4, 1);
} else {
 x_326 = x_325;
}
lean_ctor_set(x_326, 0, x_322);
lean_ctor_set(x_326, 1, x_36);
lean_ctor_set(x_326, 2, x_37);
lean_ctor_set(x_326, 3, x_38);
lean_ctor_set_uint8(x_326, sizeof(void*)*4, x_323);
x_327 = 0;
lean_ctor_set(x_206, 3, x_326);
lean_ctor_set(x_206, 2, x_321);
lean_ctor_set(x_206, 1, x_320);
lean_ctor_set(x_206, 0, x_324);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_327);
return x_206;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; 
x_328 = lean_ctor_get(x_206, 1);
x_329 = lean_ctor_get(x_206, 2);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_206);
x_330 = lean_ctor_get(x_288, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_288, 1);
lean_inc(x_331);
x_332 = lean_ctor_get(x_288, 2);
lean_inc(x_332);
x_333 = lean_ctor_get(x_288, 3);
lean_inc(x_333);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 lean_ctor_release(x_288, 2);
 lean_ctor_release(x_288, 3);
 x_334 = x_288;
} else {
 lean_dec_ref(x_288);
 x_334 = lean_box(0);
}
x_335 = 1;
lean_inc(x_207);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(1, 4, 1);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_207);
lean_ctor_set(x_336, 1, x_328);
lean_ctor_set(x_336, 2, x_329);
lean_ctor_set(x_336, 3, x_330);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_337 = x_207;
} else {
 lean_dec_ref(x_207);
 x_337 = lean_box(0);
}
lean_ctor_set_uint8(x_336, sizeof(void*)*4, x_335);
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 4, 1);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_333);
lean_ctor_set(x_338, 1, x_36);
lean_ctor_set(x_338, 2, x_37);
lean_ctor_set(x_338, 3, x_38);
lean_ctor_set_uint8(x_338, sizeof(void*)*4, x_335);
x_339 = 0;
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_336);
lean_ctor_set(x_340, 1, x_331);
lean_ctor_set(x_340, 2, x_332);
lean_ctor_set(x_340, 3, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_339);
return x_340;
}
}
else
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_206);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; 
x_342 = lean_ctor_get(x_206, 3);
lean_dec(x_342);
x_343 = lean_ctor_get(x_206, 0);
lean_dec(x_343);
x_344 = !lean_is_exclusive(x_207);
if (x_344 == 0)
{
uint8_t x_345; uint8_t x_346; 
lean_ctor_set_uint8(x_207, sizeof(void*)*4, x_299);
x_345 = 0;
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_345);
x_346 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_346);
return x_1;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; uint8_t x_353; 
x_347 = lean_ctor_get(x_207, 0);
x_348 = lean_ctor_get(x_207, 1);
x_349 = lean_ctor_get(x_207, 2);
x_350 = lean_ctor_get(x_207, 3);
lean_inc(x_350);
lean_inc(x_349);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_207);
x_351 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_351, 0, x_347);
lean_ctor_set(x_351, 1, x_348);
lean_ctor_set(x_351, 2, x_349);
lean_ctor_set(x_351, 3, x_350);
lean_ctor_set_uint8(x_351, sizeof(void*)*4, x_299);
x_352 = 0;
lean_ctor_set(x_206, 0, x_351);
lean_ctor_set_uint8(x_206, sizeof(void*)*4, x_352);
x_353 = 1;
lean_ctor_set(x_1, 0, x_206);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_353);
return x_1;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; uint8_t x_364; 
x_354 = lean_ctor_get(x_206, 1);
x_355 = lean_ctor_get(x_206, 2);
lean_inc(x_355);
lean_inc(x_354);
lean_dec(x_206);
x_356 = lean_ctor_get(x_207, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_207, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_207, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_207, 3);
lean_inc(x_359);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 lean_ctor_release(x_207, 2);
 lean_ctor_release(x_207, 3);
 x_360 = x_207;
} else {
 lean_dec_ref(x_207);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_356);
lean_ctor_set(x_361, 1, x_357);
lean_ctor_set(x_361, 2, x_358);
lean_ctor_set(x_361, 3, x_359);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_299);
x_362 = 0;
x_363 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_354);
lean_ctor_set(x_363, 2, x_355);
lean_ctor_set(x_363, 3, x_288);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = 1;
lean_ctor_set(x_1, 0, x_363);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_364);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; 
x_365 = lean_ctor_get(x_1, 0);
x_366 = lean_ctor_get(x_1, 1);
x_367 = lean_ctor_get(x_1, 2);
x_368 = lean_ctor_get(x_1, 3);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_1);
x_369 = lean_nat_dec_lt(x_2, x_366);
if (x_369 == 0)
{
uint8_t x_370; 
x_370 = lean_nat_dec_eq(x_2, x_366);
if (x_370 == 0)
{
uint8_t x_371; 
x_371 = l_Std_RBNode_isRed___rarg(x_368);
if (x_371 == 0)
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
x_372 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_368, x_2, x_3);
x_373 = 1;
x_374 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_374, 0, x_365);
lean_ctor_set(x_374, 1, x_366);
lean_ctor_set(x_374, 2, x_367);
lean_ctor_set(x_374, 3, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_368, x_2, x_3);
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_375, 3);
lean_inc(x_377);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_375, 2);
lean_inc(x_379);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_380 = x_375;
} else {
 lean_dec_ref(x_375);
 x_380 = lean_box(0);
}
x_381 = 0;
if (lean_is_scalar(x_380)) {
 x_382 = lean_alloc_ctor(1, 4, 1);
} else {
 x_382 = x_380;
}
lean_ctor_set(x_382, 0, x_377);
lean_ctor_set(x_382, 1, x_378);
lean_ctor_set(x_382, 2, x_379);
lean_ctor_set(x_382, 3, x_377);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_381);
x_383 = 1;
x_384 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_384, 0, x_365);
lean_ctor_set(x_384, 1, x_366);
lean_ctor_set(x_384, 2, x_367);
lean_ctor_set(x_384, 3, x_382);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
return x_384;
}
else
{
uint8_t x_385; 
x_385 = lean_ctor_get_uint8(x_377, sizeof(void*)*4);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; lean_object* x_398; 
x_386 = lean_ctor_get(x_375, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_375, 2);
lean_inc(x_387);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_388 = x_375;
} else {
 lean_dec_ref(x_375);
 x_388 = lean_box(0);
}
x_389 = lean_ctor_get(x_377, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_377, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_377, 2);
lean_inc(x_391);
x_392 = lean_ctor_get(x_377, 3);
lean_inc(x_392);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 lean_ctor_release(x_377, 2);
 lean_ctor_release(x_377, 3);
 x_393 = x_377;
} else {
 lean_dec_ref(x_377);
 x_393 = lean_box(0);
}
x_394 = 1;
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_365);
lean_ctor_set(x_395, 1, x_366);
lean_ctor_set(x_395, 2, x_367);
lean_ctor_set(x_395, 3, x_376);
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_388)) {
 x_396 = lean_alloc_ctor(1, 4, 1);
} else {
 x_396 = x_388;
}
lean_ctor_set(x_396, 0, x_389);
lean_ctor_set(x_396, 1, x_390);
lean_ctor_set(x_396, 2, x_391);
lean_ctor_set(x_396, 3, x_392);
lean_ctor_set_uint8(x_396, sizeof(void*)*4, x_394);
x_397 = 0;
x_398 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_386);
lean_ctor_set(x_398, 2, x_387);
lean_ctor_set(x_398, 3, x_396);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_397);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; uint8_t x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_375, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_375, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_401 = x_375;
} else {
 lean_dec_ref(x_375);
 x_401 = lean_box(0);
}
x_402 = 0;
if (lean_is_scalar(x_401)) {
 x_403 = lean_alloc_ctor(1, 4, 1);
} else {
 x_403 = x_401;
}
lean_ctor_set(x_403, 0, x_376);
lean_ctor_set(x_403, 1, x_399);
lean_ctor_set(x_403, 2, x_400);
lean_ctor_set(x_403, 3, x_377);
lean_ctor_set_uint8(x_403, sizeof(void*)*4, x_402);
x_404 = 1;
x_405 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_405, 0, x_365);
lean_ctor_set(x_405, 1, x_366);
lean_ctor_set(x_405, 2, x_367);
lean_ctor_set(x_405, 3, x_403);
lean_ctor_set_uint8(x_405, sizeof(void*)*4, x_404);
return x_405;
}
}
}
else
{
uint8_t x_406; 
x_406 = lean_ctor_get_uint8(x_376, sizeof(void*)*4);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_407 = lean_ctor_get(x_375, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_375, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_375, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_410 = x_375;
} else {
 lean_dec_ref(x_375);
 x_410 = lean_box(0);
}
x_411 = lean_ctor_get(x_376, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_376, 1);
lean_inc(x_412);
x_413 = lean_ctor_get(x_376, 2);
lean_inc(x_413);
x_414 = lean_ctor_get(x_376, 3);
lean_inc(x_414);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_415 = x_376;
} else {
 lean_dec_ref(x_376);
 x_415 = lean_box(0);
}
x_416 = 1;
if (lean_is_scalar(x_415)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_415;
}
lean_ctor_set(x_417, 0, x_365);
lean_ctor_set(x_417, 1, x_366);
lean_ctor_set(x_417, 2, x_367);
lean_ctor_set(x_417, 3, x_411);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_416);
if (lean_is_scalar(x_410)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_410;
}
lean_ctor_set(x_418, 0, x_414);
lean_ctor_set(x_418, 1, x_407);
lean_ctor_set(x_418, 2, x_408);
lean_ctor_set(x_418, 3, x_409);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_416);
x_419 = 0;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_412);
lean_ctor_set(x_420, 2, x_413);
lean_ctor_set(x_420, 3, x_418);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
else
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_375, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_375, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_375, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_424 = x_375;
} else {
 lean_dec_ref(x_375);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_376);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_365);
lean_ctor_set(x_428, 1, x_366);
lean_ctor_set(x_428, 2, x_367);
lean_ctor_set(x_428, 3, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
x_430 = lean_ctor_get(x_375, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_375, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_432 = x_375;
} else {
 lean_dec_ref(x_375);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
lean_inc(x_376);
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_365);
lean_ctor_set(x_439, 1, x_366);
lean_ctor_set(x_439, 2, x_367);
lean_ctor_set(x_439, 3, x_376);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_440 = x_376;
} else {
 lean_dec_ref(x_376);
 x_440 = lean_box(0);
}
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 4, 1);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_433);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_436);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_438);
x_442 = 0;
if (lean_is_scalar(x_432)) {
 x_443 = lean_alloc_ctor(1, 4, 1);
} else {
 x_443 = x_432;
}
lean_ctor_set(x_443, 0, x_439);
lean_ctor_set(x_443, 1, x_430);
lean_ctor_set(x_443, 2, x_431);
lean_ctor_set(x_443, 3, x_441);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_442);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; 
x_444 = lean_ctor_get(x_375, 1);
lean_inc(x_444);
x_445 = lean_ctor_get(x_375, 2);
lean_inc(x_445);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 lean_ctor_release(x_375, 2);
 lean_ctor_release(x_375, 3);
 x_446 = x_375;
} else {
 lean_dec_ref(x_375);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_376, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_376, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_376, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_376, 3);
lean_inc(x_450);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 lean_ctor_release(x_376, 2);
 lean_ctor_release(x_376, 3);
 x_451 = x_376;
} else {
 lean_dec_ref(x_376);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 4, 1);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_447);
lean_ctor_set(x_452, 1, x_448);
lean_ctor_set(x_452, 2, x_449);
lean_ctor_set(x_452, 3, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4, x_429);
x_453 = 0;
if (lean_is_scalar(x_446)) {
 x_454 = lean_alloc_ctor(1, 4, 1);
} else {
 x_454 = x_446;
}
lean_ctor_set(x_454, 0, x_452);
lean_ctor_set(x_454, 1, x_444);
lean_ctor_set(x_454, 2, x_445);
lean_ctor_set(x_454, 3, x_421);
lean_ctor_set_uint8(x_454, sizeof(void*)*4, x_453);
x_455 = 1;
x_456 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_456, 0, x_365);
lean_ctor_set(x_456, 1, x_366);
lean_ctor_set(x_456, 2, x_367);
lean_ctor_set(x_456, 3, x_454);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_455);
return x_456;
}
}
}
}
}
}
else
{
uint8_t x_457; lean_object* x_458; 
lean_dec(x_367);
lean_dec(x_366);
x_457 = 1;
x_458 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_458, 0, x_365);
lean_ctor_set(x_458, 1, x_2);
lean_ctor_set(x_458, 2, x_3);
lean_ctor_set(x_458, 3, x_368);
lean_ctor_set_uint8(x_458, sizeof(void*)*4, x_457);
return x_458;
}
}
else
{
uint8_t x_459; 
x_459 = l_Std_RBNode_isRed___rarg(x_365);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; lean_object* x_462; 
x_460 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_365, x_2, x_3);
x_461 = 1;
x_462 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_366);
lean_ctor_set(x_462, 2, x_367);
lean_ctor_set(x_462, 3, x_368);
lean_ctor_set_uint8(x_462, sizeof(void*)*4, x_461);
return x_462;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_365, x_2, x_3);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_463, 3);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; uint8_t x_469; lean_object* x_470; uint8_t x_471; lean_object* x_472; 
x_466 = lean_ctor_get(x_463, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_463, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_468 = x_463;
} else {
 lean_dec_ref(x_463);
 x_468 = lean_box(0);
}
x_469 = 0;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_465);
lean_ctor_set(x_470, 1, x_466);
lean_ctor_set(x_470, 2, x_467);
lean_ctor_set(x_470, 3, x_465);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
x_471 = 1;
x_472 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_366);
lean_ctor_set(x_472, 2, x_367);
lean_ctor_set(x_472, 3, x_368);
lean_ctor_set_uint8(x_472, sizeof(void*)*4, x_471);
return x_472;
}
else
{
uint8_t x_473; 
x_473 = lean_ctor_get_uint8(x_465, sizeof(void*)*4);
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; 
x_474 = lean_ctor_get(x_463, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_463, 2);
lean_inc(x_475);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_476 = x_463;
} else {
 lean_dec_ref(x_463);
 x_476 = lean_box(0);
}
x_477 = lean_ctor_get(x_465, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_465, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_465, 2);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 3);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 lean_ctor_release(x_465, 2);
 lean_ctor_release(x_465, 3);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
x_482 = 1;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_464);
lean_ctor_set(x_483, 1, x_474);
lean_ctor_set(x_483, 2, x_475);
lean_ctor_set(x_483, 3, x_477);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_482);
if (lean_is_scalar(x_476)) {
 x_484 = lean_alloc_ctor(1, 4, 1);
} else {
 x_484 = x_476;
}
lean_ctor_set(x_484, 0, x_480);
lean_ctor_set(x_484, 1, x_366);
lean_ctor_set(x_484, 2, x_367);
lean_ctor_set(x_484, 3, x_368);
lean_ctor_set_uint8(x_484, sizeof(void*)*4, x_482);
x_485 = 0;
x_486 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_478);
lean_ctor_set(x_486, 2, x_479);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_485);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; 
x_487 = lean_ctor_get(x_463, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_463, 2);
lean_inc(x_488);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_489 = x_463;
} else {
 lean_dec_ref(x_463);
 x_489 = lean_box(0);
}
x_490 = 0;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 4, 1);
} else {
 x_491 = x_489;
}
lean_ctor_set(x_491, 0, x_464);
lean_ctor_set(x_491, 1, x_487);
lean_ctor_set(x_491, 2, x_488);
lean_ctor_set(x_491, 3, x_465);
lean_ctor_set_uint8(x_491, sizeof(void*)*4, x_490);
x_492 = 1;
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_366);
lean_ctor_set(x_493, 2, x_367);
lean_ctor_set(x_493, 3, x_368);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_492);
return x_493;
}
}
}
else
{
uint8_t x_494; 
x_494 = lean_ctor_get_uint8(x_464, sizeof(void*)*4);
if (x_494 == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; 
x_495 = lean_ctor_get(x_463, 1);
lean_inc(x_495);
x_496 = lean_ctor_get(x_463, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_463, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_498 = x_463;
} else {
 lean_dec_ref(x_463);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_464, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_464, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_464, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_464, 3);
lean_inc(x_502);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_503 = x_464;
} else {
 lean_dec_ref(x_464);
 x_503 = lean_box(0);
}
x_504 = 1;
if (lean_is_scalar(x_503)) {
 x_505 = lean_alloc_ctor(1, 4, 1);
} else {
 x_505 = x_503;
}
lean_ctor_set(x_505, 0, x_499);
lean_ctor_set(x_505, 1, x_500);
lean_ctor_set(x_505, 2, x_501);
lean_ctor_set(x_505, 3, x_502);
lean_ctor_set_uint8(x_505, sizeof(void*)*4, x_504);
if (lean_is_scalar(x_498)) {
 x_506 = lean_alloc_ctor(1, 4, 1);
} else {
 x_506 = x_498;
}
lean_ctor_set(x_506, 0, x_497);
lean_ctor_set(x_506, 1, x_366);
lean_ctor_set(x_506, 2, x_367);
lean_ctor_set(x_506, 3, x_368);
lean_ctor_set_uint8(x_506, sizeof(void*)*4, x_504);
x_507 = 0;
x_508 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_495);
lean_ctor_set(x_508, 2, x_496);
lean_ctor_set(x_508, 3, x_506);
lean_ctor_set_uint8(x_508, sizeof(void*)*4, x_507);
return x_508;
}
else
{
lean_object* x_509; 
x_509 = lean_ctor_get(x_463, 3);
lean_inc(x_509);
if (lean_obj_tag(x_509) == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_463, 1);
lean_inc(x_510);
x_511 = lean_ctor_get(x_463, 2);
lean_inc(x_511);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_512 = x_463;
} else {
 lean_dec_ref(x_463);
 x_512 = lean_box(0);
}
x_513 = 0;
if (lean_is_scalar(x_512)) {
 x_514 = lean_alloc_ctor(1, 4, 1);
} else {
 x_514 = x_512;
}
lean_ctor_set(x_514, 0, x_464);
lean_ctor_set(x_514, 1, x_510);
lean_ctor_set(x_514, 2, x_511);
lean_ctor_set(x_514, 3, x_509);
lean_ctor_set_uint8(x_514, sizeof(void*)*4, x_513);
x_515 = 1;
x_516 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_366);
lean_ctor_set(x_516, 2, x_367);
lean_ctor_set(x_516, 3, x_368);
lean_ctor_set_uint8(x_516, sizeof(void*)*4, x_515);
return x_516;
}
else
{
uint8_t x_517; 
x_517 = lean_ctor_get_uint8(x_509, sizeof(void*)*4);
if (x_517 == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; lean_object* x_531; 
x_518 = lean_ctor_get(x_463, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_463, 2);
lean_inc(x_519);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_520 = x_463;
} else {
 lean_dec_ref(x_463);
 x_520 = lean_box(0);
}
x_521 = lean_ctor_get(x_509, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_509, 1);
lean_inc(x_522);
x_523 = lean_ctor_get(x_509, 2);
lean_inc(x_523);
x_524 = lean_ctor_get(x_509, 3);
lean_inc(x_524);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 lean_ctor_release(x_509, 2);
 lean_ctor_release(x_509, 3);
 x_525 = x_509;
} else {
 lean_dec_ref(x_509);
 x_525 = lean_box(0);
}
x_526 = 1;
lean_inc(x_464);
if (lean_is_scalar(x_525)) {
 x_527 = lean_alloc_ctor(1, 4, 1);
} else {
 x_527 = x_525;
}
lean_ctor_set(x_527, 0, x_464);
lean_ctor_set(x_527, 1, x_518);
lean_ctor_set(x_527, 2, x_519);
lean_ctor_set(x_527, 3, x_521);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_528 = x_464;
} else {
 lean_dec_ref(x_464);
 x_528 = lean_box(0);
}
lean_ctor_set_uint8(x_527, sizeof(void*)*4, x_526);
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 4, 1);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_524);
lean_ctor_set(x_529, 1, x_366);
lean_ctor_set(x_529, 2, x_367);
lean_ctor_set(x_529, 3, x_368);
lean_ctor_set_uint8(x_529, sizeof(void*)*4, x_526);
x_530 = 0;
if (lean_is_scalar(x_520)) {
 x_531 = lean_alloc_ctor(1, 4, 1);
} else {
 x_531 = x_520;
}
lean_ctor_set(x_531, 0, x_527);
lean_ctor_set(x_531, 1, x_522);
lean_ctor_set(x_531, 2, x_523);
lean_ctor_set(x_531, 3, x_529);
lean_ctor_set_uint8(x_531, sizeof(void*)*4, x_530);
return x_531;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; uint8_t x_543; lean_object* x_544; 
x_532 = lean_ctor_get(x_463, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_463, 2);
lean_inc(x_533);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 lean_ctor_release(x_463, 2);
 lean_ctor_release(x_463, 3);
 x_534 = x_463;
} else {
 lean_dec_ref(x_463);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_464, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_464, 1);
lean_inc(x_536);
x_537 = lean_ctor_get(x_464, 2);
lean_inc(x_537);
x_538 = lean_ctor_get(x_464, 3);
lean_inc(x_538);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 lean_ctor_release(x_464, 2);
 lean_ctor_release(x_464, 3);
 x_539 = x_464;
} else {
 lean_dec_ref(x_464);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 4, 1);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_535);
lean_ctor_set(x_540, 1, x_536);
lean_ctor_set(x_540, 2, x_537);
lean_ctor_set(x_540, 3, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*4, x_517);
x_541 = 0;
if (lean_is_scalar(x_534)) {
 x_542 = lean_alloc_ctor(1, 4, 1);
} else {
 x_542 = x_534;
}
lean_ctor_set(x_542, 0, x_540);
lean_ctor_set(x_542, 1, x_532);
lean_ctor_set(x_542, 2, x_533);
lean_ctor_set(x_542, 3, x_509);
lean_ctor_set_uint8(x_542, sizeof(void*)*4, x_541);
x_543 = 1;
x_544 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_366);
lean_ctor_set(x_544, 2, x_367);
lean_ctor_set(x_544, 3, x_368);
lean_ctor_set_uint8(x_544, sizeof(void*)*4, x_543);
return x_544;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Std_RBNode_ins___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__2(x_1, x_2, x_3);
x_7 = l_Std_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_10, x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(x_21, x_1, x_13);
lean_ctor_set(x_18, 0, x_22);
x_23 = lean_st_ref_set(x_6, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(x_30, x_1, x_13);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_st_ref_set(x_6, x_33, x_19);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addTermInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_PrettyPrinter_Delaborator_addTermInfo(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set(x_13, 4, x_3);
x_14 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_13 = l_Lean_PrettyPrinter_Delaborator_addFieldInfo_mkFieldInfo(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_7, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(x_22, x_1, x_14);
lean_ctor_set(x_19, 0, x_23);
x_24 = lean_st_ref_set(x_7, x_19, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = l_Std_RBNode_insert___at_Lean_PrettyPrinter_Delaborator_addTermInfo___spec__1(x_31, x_1, x_14);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_st_ref_set(x_7, x_34, x_20);
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
x_38 = lean_box(0);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_addFieldInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_PrettyPrinter_Delaborator_addFieldInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_12 = lean_apply_7(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_12, 1);
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_23 = lean_nat_dec_eq(x_22, x_21);
lean_dec(x_21);
if (x_23 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
else
{
lean_free_object(x_12);
lean_dec(x_13);
x_1 = x_11;
x_8 = x_19;
goto _start;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
x_27 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_28 = lean_nat_dec_eq(x_27, x_26);
lean_dec(x_26);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_dec(x_13);
x_1 = x_11;
x_8 = x_25;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delabAttribute;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delabFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_8);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_st_ref_get(x_7, x_8);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1;
lean_inc(x_1);
x_27 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_26, x_25, x_1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_List_firstM___at_Lean_PrettyPrinter_Delaborator_delabFor___spec__1(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___at_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 0;
lean_inc(x_32);
x_41 = l_Lean_PrettyPrinter_Delaborator_addTermInfo(x_35, x_32, x_38, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_32);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_9 = x_46;
x_10 = x_47;
goto block_20;
}
}
block_20:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_14 = lean_nat_dec_eq(x_13, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_9);
x_16 = l_Lean_Name_isAtomic(x_1);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Name_getRoot(x_1);
lean_dec(x_1);
x_1 = x_17;
x_8 = x_10;
goto _start;
}
else
{
lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = l_Lean_PrettyPrinter_Delaborator_failure___rarg(x_10);
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_delab___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_SubExpr_Pos_push(x_13, x_2);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 4, x_15);
x_16 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 2);
x_20 = lean_ctor_get(x_4, 3);
x_21 = lean_ctor_get_uint8(x_4, sizeof(void*)*5);
x_22 = lean_ctor_get(x_4, 4);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_SubExpr_Pos_push(x_23, x_2);
lean_dec(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_26, 0, x_17);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*5, x_21);
x_27 = lean_apply_7(x_3, x_26, x_5, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = lean_infer_type(x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_SubExpr_Pos_typeCoord;
x_16 = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___at_Lean_PrettyPrinter_Delaborator_delab___spec__2(x_13, x_15, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 5);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_SourceInfo_fromRef(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delab), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Parser", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__6;
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Term", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3;
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("paren", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5;
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("(", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("null", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("typeAscription", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5;
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(")", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPAnalyzeTypeAscriptions___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPAnalysisNeedsType___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("don't know how to delaborate '", 30);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("'", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_83; 
x_10 = l_Lean_PrettyPrinter_Delaborator_getExprKind(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_83 = l_Lean_PrettyPrinter_Delaborator_delabFor(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_11);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_14 = x_84;
x_15 = x_85;
goto block_82;
}
else
{
lean_object* x_86; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_83, 0);
lean_dec(x_88);
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_83, 1);
x_93 = lean_ctor_get(x_83, 0);
lean_dec(x_93);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
x_95 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_96 = lean_nat_dec_eq(x_95, x_94);
lean_dec(x_94);
if (x_96 == 0)
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_83;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_free_object(x_83);
lean_dec(x_86);
x_97 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_97, 0, x_11);
x_98 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4(x_101, x_5, x_6, x_7, x_8, x_92);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_83, 1);
lean_inc(x_107);
lean_dec(x_83);
x_108 = lean_ctor_get(x_86, 0);
lean_inc(x_108);
x_109 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_110 = lean_nat_dec_eq(x_109, x_108);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_86);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_86);
x_112 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_112, 0, x_11);
x_113 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21;
x_114 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_115 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23;
x_116 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4(x_116, x_5, x_6, x_7, x_8, x_107);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_120 = x_117;
} else {
 lean_dec_ref(x_117);
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
}
}
block_82:
{
uint8_t x_16; lean_object* x_17; lean_object* x_57; lean_object* x_58; 
x_57 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_57, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_unbox(x_59);
lean_dec(x_59);
x_16 = x_62;
x_17 = x_61;
goto block_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
lean_dec(x_58);
x_64 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_65 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_64, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_unbox(x_66);
lean_dec(x_66);
x_16 = x_69;
x_17 = x_68;
goto block_56;
}
else
{
lean_object* x_70; uint8_t x_71; 
lean_dec(x_66);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = l_Lean_Expr_isMData(x_1);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = 1;
x_16 = x_72;
x_17 = x_70;
goto block_56;
}
else
{
uint8_t x_73; 
x_73 = 0;
x_16 = x_73;
x_17 = x_70;
goto block_56;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_65);
if (x_74 == 0)
{
return x_65;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_65, 0);
x_76 = lean_ctor_get(x_65, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_65);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_58);
if (x_78 == 0)
{
return x_58;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_58, 0);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_58);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
block_56:
{
if (x_16 == 0)
{
lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_13)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_13;
}
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_20 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
x_23 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8;
lean_inc(x_24);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13;
lean_inc(x_24);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14;
x_31 = lean_array_push(x_30, x_29);
x_32 = lean_array_push(x_31, x_21);
x_33 = lean_box(2);
x_34 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12;
x_35 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
x_36 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
x_37 = lean_array_push(x_36, x_35);
x_38 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10;
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_array_push(x_30, x_14);
x_41 = lean_array_push(x_40, x_39);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16;
x_44 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17;
x_46 = lean_array_push(x_45, x_27);
x_47 = lean_array_push(x_46, x_42);
x_48 = lean_array_push(x_47, x_44);
x_49 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7;
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
x_51 = l_Lean_PrettyPrinter_Delaborator_annotateCurPos(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPProofs___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_getPPProofsWithType___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("hole", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5;
x_2 = l_Lean_PrettyPrinter_Delaborator_delab___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_", 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
x_9 = l_Lean_Core_checkMaxHeartbeats(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___at_Lean_PrettyPrinter_Delaborator_getExprKind___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_Delaborator_delab___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_isAtomic(x_12);
if (x_18 == 0)
{
uint8_t x_128; 
x_128 = lean_unbox(x_16);
lean_dec(x_16);
if (x_128 == 0)
{
lean_object* x_129; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
x_129 = l_Lean_Meta_isProof(x_12, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_unbox(x_130);
lean_dec(x_130);
x_19 = x_132;
x_20 = x_131;
goto block_127;
}
else
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_dec(x_129);
x_134 = 0;
x_19 = x_134;
x_20 = x_133;
goto block_127;
}
}
else
{
uint8_t x_135; 
x_135 = 0;
x_19 = x_135;
x_20 = x_17;
goto block_127;
}
}
else
{
uint8_t x_136; 
lean_dec(x_16);
x_136 = 0;
x_19 = x_136;
x_20 = x_17;
goto block_127;
}
block_127:
{
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1(x_12, x_21, x_1, x_2, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_12);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_23 = l_Lean_PrettyPrinter_Delaborator_delab___closed__2;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_PrettyPrinter_Delaborator_getPPOption(x_23, x_1, x_2, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(x_5, x_6, x_27);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l_Lean_PrettyPrinter_Delaborator_delab___closed__5;
x_32 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_box(2);
x_36 = l_Lean_PrettyPrinter_Delaborator_delab___closed__4;
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
lean_ctor_set(x_28, 0, x_37);
return x_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_28, 0);
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_28);
x_40 = l_Lean_PrettyPrinter_Delaborator_delab___closed__5;
x_41 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
x_43 = lean_array_push(x_42, x_41);
x_44 = lean_box(2);
x_45 = l_Lean_PrettyPrinter_Delaborator_delab___closed__4;
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_39);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_dec(x_24);
x_49 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1;
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___at_Lean_PrettyPrinter_Delaborator_delab___spec__1(x_49, x_1, x_2, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(x_5, x_6, x_52);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8;
lean_inc(x_55);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_PrettyPrinter_Delaborator_delab___closed__5;
lean_inc(x_55);
x_59 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
x_61 = lean_array_push(x_60, x_59);
x_62 = lean_box(2);
x_63 = l_Lean_PrettyPrinter_Delaborator_delab___closed__4;
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_64, 2, x_61);
x_65 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13;
lean_inc(x_55);
x_66 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14;
x_68 = lean_array_push(x_67, x_66);
x_69 = lean_array_push(x_68, x_51);
x_70 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12;
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_69);
x_72 = lean_array_push(x_60, x_71);
x_73 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10;
x_74 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_74, 0, x_62);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_74, 2, x_72);
x_75 = lean_array_push(x_67, x_64);
x_76 = lean_array_push(x_75, x_74);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_76);
x_78 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16;
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_55);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17;
x_81 = lean_array_push(x_80, x_57);
x_82 = lean_array_push(x_81, x_77);
x_83 = lean_array_push(x_82, x_79);
x_84 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7;
x_85 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_85, 0, x_62);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_83);
lean_ctor_set(x_53, 0, x_85);
return x_53;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_86 = lean_ctor_get(x_53, 0);
x_87 = lean_ctor_get(x_53, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_53);
x_88 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8;
lean_inc(x_86);
x_89 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_PrettyPrinter_Delaborator_delab___closed__5;
lean_inc(x_86);
x_91 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15;
x_93 = lean_array_push(x_92, x_91);
x_94 = lean_box(2);
x_95 = l_Lean_PrettyPrinter_Delaborator_delab___closed__4;
x_96 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
lean_ctor_set(x_96, 2, x_93);
x_97 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13;
lean_inc(x_86);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_86);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14;
x_100 = lean_array_push(x_99, x_98);
x_101 = lean_array_push(x_100, x_51);
x_102 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12;
x_103 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set(x_103, 2, x_101);
x_104 = lean_array_push(x_92, x_103);
x_105 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10;
x_106 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_104);
x_107 = lean_array_push(x_99, x_96);
x_108 = lean_array_push(x_107, x_106);
x_109 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_109, 0, x_94);
lean_ctor_set(x_109, 1, x_105);
lean_ctor_set(x_109, 2, x_108);
x_110 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16;
x_111 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_111, 0, x_86);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17;
x_113 = lean_array_push(x_112, x_89);
x_114 = lean_array_push(x_113, x_109);
x_115 = lean_array_push(x_114, x_111);
x_116 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7;
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_94);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_115);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_87);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_dec(x_6);
lean_dec(x_5);
x_119 = !lean_is_exclusive(x_50);
if (x_119 == 0)
{
return x_50;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_50, 0);
x_121 = lean_ctor_get(x_50, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_50);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_24);
if (x_123 == 0)
{
return x_24;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_24, 0);
x_125 = lean_ctor_get(x_24, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_24);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_15);
if (x_137 == 0)
{
return x_15;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_15, 0);
x_139 = lean_ctor_get(x_15, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_15);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_9);
if (x_141 == 0)
{
return x_9;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_9, 0);
x_143 = lean_ctor_get(x_9, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_9);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MonadRef_mkInfoFromRefPos___at_Lean_PrettyPrinter_Delaborator_delab___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_Delaborator_delab___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ambiguous identifier '", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("', possible interpretations: ", 29);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l_Lean_resolveGlobalConstCore___at_Lean_registerInitAttrUnsafe___spec__8(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_Lean_mkConst(x_1, x_8);
x_10 = lean_expr_dbg_to_string(x_9);
lean_dec(x_9);
x_11 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverloadCore___spec__1(x_8, x_6, x_8);
x_16 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(x_21, x_2, x_3, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_26);
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
lean_dec(x_5);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
lean_dec(x_6);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_23);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_31 = lean_box(0);
x_32 = l_Lean_mkConst(x_1, x_31);
x_33 = lean_expr_dbg_to_string(x_32);
lean_dec(x_32);
x_34 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1;
x_35 = lean_string_append(x_34, x_33);
lean_dec(x_33);
x_36 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = l_List_mapTRAux___at_Lean_resolveGlobalConstNoOverloadCore___spec__1(x_31, x_6, x_31);
x_39 = l_List_toString___at_Lean_resolveGlobalConstNoOverloadCore___spec__2(x_38);
x_40 = lean_string_append(x_37, x_39);
lean_dec(x_39);
x_41 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lean_throwError___at_Lean_registerInitAttrUnsafe___spec__3(x_44, x_2, x_3, x_30);
lean_dec(x_3);
lean_dec(x_2);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_5);
if (x_46 == 0)
{
return x_5;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_5, 0);
x_48 = lean_ctor_get(x_5, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_5);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Attribute_Builtin_getId(x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1(x_7, x_3, x_4, x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_4);
lean_dec(x_3);
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("appUnexpander", 13);
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
x_1 = lean_mk_string_from_bytes("Unexpander", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__8;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Register an unexpander for applications of a given constant.\n\n[appUnexpander c] registers a `Lean.PrettyPrinter.Unexpander` for applications of the constant `c`. The unexpander is\npassed the result of pre-pretty printing the application *without* implicitly passed arguments. If `pp.explicit` is set\nto true or `pp.notation` is set to false, it will not be called at all.", 371);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1___boxed), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__2;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__5;
x_4 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__4;
x_5 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__6;
x_6 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__15;
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
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("appUnexpanderAttribute", 22);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__10;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__8;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__7;
x_3 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9;
x_4 = l_Lean_KeyedDeclsAttribute_init___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___lambda__1(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_PrettyPrinter_delabCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_KVMap_findCore(x_1, x_3);
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
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 0);
if (lean_obj_tag(x_7) == 1)
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_ctor_get_uint8(x_7, 0);
lean_dec(x_7);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; 
lean_free_object(x_4);
lean_dec(x_7);
x_10 = lean_box(0);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
if (lean_obj_tag(x_11) == 1)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get_uint8(x_11, 0);
lean_dec(x_11);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_box(0);
return x_15;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_unbox(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_unbox(x_8);
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
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.Delaborator.Basic", 36);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.PrettyPrinter.delabCore", 28);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2;
x_2 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3;
x_3 = lean_unsigned_to_nat(301u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_22 = lean_ctor_get(x_7, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_7, 7);
lean_inc(x_23);
x_24 = l_Lean_Options_getInPattern(x_1);
x_25 = l_Lean_SubExpr_Pos_root;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*5, x_24);
x_28 = lean_st_ref_get(x_8, x_9);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1;
x_31 = lean_st_mk_ref(x_30, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_32);
x_34 = lean_apply_7(x_3, x_27, x_32, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_8, x_36);
lean_dec(x_8);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_st_ref_get(x_32, x_38);
lean_dec(x_32);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_40);
x_10 = x_42;
x_11 = x_41;
goto block_21;
}
else
{
lean_object* x_43; 
lean_dec(x_32);
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_34);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_34, 0);
lean_dec(x_45);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_34, 1);
x_50 = lean_ctor_get(x_34, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
x_52 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_53 = lean_nat_dec_eq(x_52, x_51);
lean_dec(x_51);
if (x_53 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_34);
lean_dec(x_43);
x_54 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5;
x_55 = l_panic___at_Lean_PrettyPrinter_delabCore___spec__1(x_54, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_10 = x_56;
x_11 = x_57;
goto block_21;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_34, 1);
lean_inc(x_62);
lean_dec(x_34);
x_63 = lean_ctor_get(x_43, 0);
lean_inc(x_63);
x_64 = l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1;
x_65 = lean_nat_dec_eq(x_64, x_63);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_43);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_43);
x_67 = l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5;
x_68 = l_panic___at_Lean_PrettyPrinter_delabCore___spec__1(x_67, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_10 = x_69;
x_11 = x_70;
goto block_21;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_73 = x_68;
} else {
 lean_dec_ref(x_68);
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
block_21:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_ctor_set(x_10, 1, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_10, 1);
x_17 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_getPPAll(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_getPPAnalyze(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_delabCore___lambda__1(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 6);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 7);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 8);
lean_inc(x_20);
x_21 = lean_ctor_get(x_7, 9);
lean_inc(x_21);
x_22 = lean_ctor_get(x_7, 10);
lean_inc(x_22);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_1);
lean_ctor_set(x_23, 3, x_15);
lean_ctor_set(x_23, 4, x_16);
lean_ctor_set(x_23, 5, x_17);
lean_ctor_set(x_23, 6, x_18);
lean_ctor_set(x_23, 7, x_19);
lean_ctor_set(x_23, 8, x_20);
lean_ctor_set(x_23, 9, x_21);
lean_ctor_set(x_23, 10, x_22);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_24 = l_Lean_PrettyPrinter_Delaborator_topDownAnalyze(x_4, x_5, x_6, x_23, x_8, x_9);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_PrettyPrinter_delabCore___lambda__1(x_1, x_4, x_2, x_25, x_5, x_6, x_7, x_8, x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_PrettyPrinter_delabCore___lambda__1(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_28;
}
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_PrettyPrinter_delabCore___lambda__1(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = l_Lean_getPPInstantiateMVars(x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lean_PrettyPrinter_delabCore___lambda__2(x_4, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_3, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_PrettyPrinter_delabCore___lambda__2(x_4, x_1, x_2, x_14, x_6, x_7, x_8, x_9, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_pp_proofs;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1;
x_12 = l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2(x_10, x_11);
x_13 = lean_box(0);
x_14 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_PrettyPrinter_delabCore___lambda__3(x_1, x_2, x_3, x_10, x_15, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
else
{
lean_object* x_17; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_Lean_Meta_isProof(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_PrettyPrinter_delabCore___lambda__3(x_1, x_2, x_3, x_10, x_21, x_5, x_6, x_7, x_8, x_20);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = 1;
x_25 = l_Lean_Option_set___at_Lean_Meta_withPPInaccessibleNamesImp___spec__2(x_10, x_11, x_24);
x_26 = lean_box(0);
x_27 = l_Lean_PrettyPrinter_delabCore___lambda__3(x_1, x_2, x_3, x_25, x_26, x_5, x_6, x_7, x_8, x_23);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_box(0);
x_30 = l_Lean_PrettyPrinter_delabCore___lambda__3(x_1, x_2, x_3, x_10, x_29, x_5, x_6, x_7, x_8, x_28);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_eraseInaccessibleAnnotations___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_erasePatternRefAnnotations___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_delabCore___closed__3;
x_2 = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("input", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_delabCore___closed__4;
x_2 = l_Lean_PrettyPrinter_delabCore___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_delabCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delabCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_PrettyPrinter_delabCore___closed__1;
x_10 = l_Lean_PrettyPrinter_delabCore___closed__2;
lean_inc(x_7);
lean_inc(x_6);
x_11 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_1, x_9, x_10, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_delabCore___closed__6;
x_30 = lean_st_ref_get(x_7, x_13);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 0;
x_15 = x_35;
x_16 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_14, x_4, x_5, x_6, x_7, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_15 = x_40;
x_16 = x_39;
goto block_29;
}
block_29:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_PrettyPrinter_delabCore___lambda__4(x_3, x_2, x_12, x_17, x_4, x_5, x_6, x_7, x_16);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_expr_dbg_to_string(x_12);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_PrettyPrinter_delabCore___closed__7;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_24, x_4, x_5, x_6, x_7, x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_PrettyPrinter_delabCore___lambda__4(x_3, x_2, x_12, x_26, x_4, x_5, x_6, x_7, x_27);
return x_28;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get_x3f___at_Lean_PrettyPrinter_delabCore___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_800____at_Lean_PrettyPrinter_delabCore___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_delab(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1;
x_9 = l_Lean_PrettyPrinter_delabCore(x_1, x_2, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
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
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2830_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_delabCore___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Syntax(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Term(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_AuxDiscr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_SubExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_AuxDiscr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Delaborator_TopDownAnalyze(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_Delaborator_Context_inPattern___default = _init_l_Lean_PrettyPrinter_Delaborator_Context_inPattern___default();
l_Lean_PrettyPrinter_Delaborator_State_infos___default = _init_l_Lean_PrettyPrinter_Delaborator_State_infos___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_State_infos___default);
l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_State_holeIter___default___closed__1);
l_Lean_PrettyPrinter_Delaborator_State_holeIter___default = _init_l_Lean_PrettyPrinter_Delaborator_State_holeIter___default();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_State_holeIter___default);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__1);
l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96____closed__2);
if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_96_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabFailureId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabFailureId);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instInhabitedDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_orElse___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_failure___rarg___closed__1);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__3);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__4);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__5);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM___closed__6);
l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instAlternativeDelabM);
l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instOrElseDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadReaderOfSubExprDelabM);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__1);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__2);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__3);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__4);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__5);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM___closed__6);
l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM = _init_l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadStateOfHoleIteratorDelabM);
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
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__6);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__7);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__8);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__9);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__10);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__11);
l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12 = _init_l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_instMonadQuotationDelabM___closed__12);
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
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__16);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__17);
l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18 = _init_l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute___closed__18);
if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_mkDelabAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_delabAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabAttribute);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__1();
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
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__12);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__13);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__14);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__15);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__16);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__17);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__18);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__19);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__20);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__21);
l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22 = _init_l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getExprKind___closed__22);
l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getOptionsAtCurrPos___closed__1);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__1);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__2);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__3);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__4);
l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_getUnusedName___closed__5);
l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_addTermInfo_mkTermInfo___closed__1);
l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delabFor___closed__1);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__1);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__2);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__3);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__4);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__5);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__6);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__7);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__8);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__9);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__10);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__11);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__12);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__13);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__14);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__15);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__16);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__17);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__18);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__19);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__20);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__21);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__22);
l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23 = _init_l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___lambda__1___closed__23);
l_Lean_PrettyPrinter_Delaborator_delab___closed__1 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__1);
l_Lean_PrettyPrinter_Delaborator_delab___closed__2 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__2);
l_Lean_PrettyPrinter_Delaborator_delab___closed__3 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__3);
l_Lean_PrettyPrinter_Delaborator_delab___closed__4 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__4);
l_Lean_PrettyPrinter_Delaborator_delab___closed__5 = _init_l_Lean_PrettyPrinter_Delaborator_delab___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_delab___closed__5);
l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1 = _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__1);
l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2 = _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__2);
l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3 = _init_l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3();
lean_mark_persistent(l_Lean_resolveGlobalConstNoOverloadCore___at_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___spec__1___closed__3);
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
l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9 = _init_l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute___closed__9);
if (builtin) {res = l_Lean_PrettyPrinter_Delaborator_mkAppUnexpanderAttribute(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_appUnexpanderAttribute);
lean_dec_ref(res);
}l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1 = _init_l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_PrettyPrinter_delabCore___spec__1___closed__1);
l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1 = _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__1___closed__1);
l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2 = _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__1___closed__2);
l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3 = _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__1___closed__3);
l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4 = _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__1___closed__4);
l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5 = _init_l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__1___closed__5);
l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1 = _init_l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___lambda__4___closed__1);
l_Lean_PrettyPrinter_delabCore___closed__1 = _init_l_Lean_PrettyPrinter_delabCore___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__1);
l_Lean_PrettyPrinter_delabCore___closed__2 = _init_l_Lean_PrettyPrinter_delabCore___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__2);
l_Lean_PrettyPrinter_delabCore___closed__3 = _init_l_Lean_PrettyPrinter_delabCore___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__3);
l_Lean_PrettyPrinter_delabCore___closed__4 = _init_l_Lean_PrettyPrinter_delabCore___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__4);
l_Lean_PrettyPrinter_delabCore___closed__5 = _init_l_Lean_PrettyPrinter_delabCore___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__5);
l_Lean_PrettyPrinter_delabCore___closed__6 = _init_l_Lean_PrettyPrinter_delabCore___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__6);
l_Lean_PrettyPrinter_delabCore___closed__7 = _init_l_Lean_PrettyPrinter_delabCore___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_delabCore___closed__7);
res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Delaborator_Basic___hyg_2830_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
